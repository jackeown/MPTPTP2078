%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 (1089 expanded)
%              Number of leaves         :   12 ( 219 expanded)
%              Depth                    :   27
%              Number of atoms          :  389 (4478 expanded)
%              Number of equality atoms :   47 ( 787 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f223,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f213,f222])).

fof(f222,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f219,f32])).

fof(f32,plain,(
    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f219,plain,
    ( k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | spl4_9 ),
    inference(resolution,[],[f172,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f172,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_9
  <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f213,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f211,f109])).

fof(f109,plain,(
    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f108,f88])).

fof(f88,plain,(
    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f86,f32])).

fof(f86,plain,
    ( sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f85,f44])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
      | sK2(X0,sK0,k2_struct_0(sK0)) = X0 ) ),
    inference(forward_demodulation,[],[f84,f77])).

fof(f77,plain,(
    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f76,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f34,f33])).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(forward_demodulation,[],[f75,f59])).

fof(f59,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f35,f58])).

fof(f58,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f36,f31])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f74,f31])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f73,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f72,f29])).

fof(f29,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f71,f28])).

fof(f28,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f84,plain,(
    ! [X0] :
      ( sK2(X0,sK0,k2_struct_0(sK0)) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f83,f57])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f82,f59])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f81,f31])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f80,f27])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f79,f29])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f78,f28])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f51,f30])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f108,plain,(
    m1_subset_1(sK2(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f106,f32])).

fof(f106,plain,
    ( m1_subset_1(sK2(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f105,f44])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
      | m1_subset_1(sK2(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f104,f77])).

fof(f104,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f103,f57])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK2(X1,sK0,X0),k2_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f102,f59])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f101,f59])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f100,f31])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f99,f27])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f98,f29])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f97,f28])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f50,f30])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f211,plain,
    ( ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f210,f62])).

fof(f62,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f61,f27])).

fof(f61,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f60,f58])).

fof(f60,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f41,f59])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f210,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl4_9 ),
    inference(resolution,[],[f209,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f209,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f208,f173])).

fof(f173,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f208,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f207,f77])).

fof(f207,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f206,f57])).

fof(f206,plain,
    ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f205,f116])).

fof(f116,plain,(
    ~ r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) ),
    inference(resolution,[],[f109,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | ~ r2_orders_2(sK0,X0,X0) ) ),
    inference(forward_demodulation,[],[f63,f59])).

fof(f63,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X0,X0) ) ),
    inference(resolution,[],[f56,f31])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | X1 != X2
      | ~ r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
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
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f205,plain,
    ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) ),
    inference(superposition,[],[f204,f88])).

fof(f204,plain,(
    ! [X0,X1] :
      ( r2_orders_2(sK0,sK2(X1,sK0,X0),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
      | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f203,f109])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,sK2(X2,sK0,X0),X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f202,f59])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,sK2(X2,sK0,X0),X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f201,f59])).

fof(f201,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,sK2(X2,sK0,X0),X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f200,f31])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,sK2(X2,sK0,X0),X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f199,f27])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,sK2(X2,sK0,X0),X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f198,f29])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,sK2(X2,sK0,X0),X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f197,f28])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,sK2(X2,sK0,X0),X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f49,f30])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | r2_orders_2(X1,sK2(X0,X1,X2),X4)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (8065)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (8065)Refutation not found, incomplete strategy% (8065)------------------------------
% 0.21/0.52  % (8065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8065)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8065)Memory used [KB]: 10618
% 0.21/0.52  % (8065)Time elapsed: 0.088 s
% 0.21/0.52  % (8065)------------------------------
% 0.21/0.52  % (8065)------------------------------
% 0.21/0.52  % (8081)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (8081)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f223,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f213,f222])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    spl4_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f221])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    $false | spl4_9),
% 0.21/0.53    inference(subsumption_resolution,[],[f219,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | spl4_9),
% 0.21/0.53    inference(resolution,[],[f172,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f171])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    spl4_9 <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ~spl4_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f212])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    $false | ~spl4_9),
% 0.21/0.53    inference(subsumption_resolution,[],[f211,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.21/0.53    inference(forward_demodulation,[],[f108,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f86,f32])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK2(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.53    inference(resolution,[],[f85,f44])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | sK2(X0,sK0,k2_struct_0(sK0)) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f84,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.53    inference(resolution,[],[f76,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f34,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f75,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f35,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    l1_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f36,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    l1_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f74,f31])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f73,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f72,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    v4_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f71,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    v3_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f40,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    v5_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v5_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0] : (sK2(X0,sK0,k2_struct_0(sK0)) = X0 | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))) )),
% 0.21/0.53    inference(resolution,[],[f83,f57])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f82,f59])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f81,f31])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f80,f27])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f79,f29])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f78,f28])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK2(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(resolution,[],[f51,f30])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_1_orders_2(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    m1_subset_1(sK2(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f106,f32])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    m1_subset_1(sK2(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.21/0.53    inference(resolution,[],[f105,f44])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(sK2(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f104,f77])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK2(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))) )),
% 0.21/0.53    inference(resolution,[],[f103,f57])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK2(X1,sK0,X0),k2_struct_0(sK0)) | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f102,f59])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0)) | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f101,f59])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0)) | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f100,f31])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0)) | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f99,f27])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0)) | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f98,f29])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0)) | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f97,f28])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(X1,sK0,X0),u1_struct_0(sK0)) | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(resolution,[],[f50,f30])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl4_9),
% 0.21/0.53    inference(subsumption_resolution,[],[f210,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f61,f27])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ~v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f60,f58])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(superposition,[],[f41,f59])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl4_9),
% 0.21/0.53    inference(resolution,[],[f209,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl4_9),
% 0.21/0.53    inference(subsumption_resolution,[],[f208,f173])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | ~spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f171])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.21/0.53    inference(forward_demodulation,[],[f207,f77])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f206,f57])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f205,f116])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ~r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))),
% 0.21/0.53    inference(resolution,[],[f109,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_orders_2(sK0,X0,X0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f63,f59])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f56,f31])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.21/0.53    inference(equality_resolution,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | X1 != X2 | ~r2_orders_2(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))),
% 0.21/0.53    inference(superposition,[],[f204,f88])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_orders_2(sK0,sK2(X1,sK0,X0),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X1,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(resolution,[],[f203,f109])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,sK2(X2,sK0,X0),X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f202,f59])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,sK2(X2,sK0,X0),X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f201,f59])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,sK2(X2,sK0,X0),X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f200,f31])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,sK2(X2,sK0,X0),X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f199,f27])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,sK2(X2,sK0,X0),X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f198,f29])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,sK2(X2,sK0,X0),X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f197,f28])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,sK2(X2,sK0,X0),X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X0))) )),
% 0.21/0.53    inference(resolution,[],[f49,f30])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (~v5_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~r2_hidden(X4,X2) | r2_orders_2(X1,sK2(X0,X1,X2),X4) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (8081)------------------------------
% 0.21/0.53  % (8081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8081)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (8081)Memory used [KB]: 10746
% 0.21/0.53  % (8081)Time elapsed: 0.102 s
% 0.21/0.53  % (8081)------------------------------
% 0.21/0.53  % (8081)------------------------------
% 0.21/0.53  % (8058)Success in time 0.172 s
%------------------------------------------------------------------------------
