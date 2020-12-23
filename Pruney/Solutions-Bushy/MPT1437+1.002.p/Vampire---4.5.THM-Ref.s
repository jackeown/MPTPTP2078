%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1437+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 633 expanded)
%              Number of leaves         :   13 ( 135 expanded)
%              Depth                    :   20
%              Number of atoms          :  333 (2976 expanded)
%              Number of equality atoms :   39 ( 135 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f527,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f171,f322,f339,f343,f348,f515,f520,f526])).

fof(f526,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f35,f168,f164])).

fof(f164,plain,
    ( spl6_1
  <=> r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f168,plain,
    ( spl6_2
  <=> r3_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f35,plain,
    ( ~ r3_lattices(sK0,sK1,sK2)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <~> r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <~> r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
                <=> r3_lattices(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_filter_1)).

fof(f520,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f159,f312])).

fof(f312,plain,
    ( spl6_6
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f159,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f69,f142])).

fof(f142,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f105,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l2_lattices(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l2_lattices)).

fof(f105,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f40,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f40,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
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

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f515,plain,
    ( spl6_2
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f169,f501])).

fof(f501,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f494,f337])).

fof(f337,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl6_8
  <=> r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f494,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK0))
      | r3_lattices(sK0,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f493])).

fof(f493,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,X1)
      | ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK0))
      | ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK0)) ) ),
    inference(superposition,[],[f376,f421])).

fof(f421,plain,(
    ! [X0,X1] :
      ( sK4(k4_tarski(X0,X1),sK0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK0)) ) ),
    inference(equality_resolution,[],[f361])).

fof(f361,plain,(
    ! [X6,X8,X7] :
      ( k4_tarski(X7,X8) != X6
      | sK4(X6,sK0) = X8
      | ~ r2_hidden(X6,k8_filter_1(sK0)) ) ),
    inference(superposition,[],[f61,f356])).

fof(f356,plain,(
    ! [X2] :
      ( k4_tarski(sK3(X2,sK0),sK4(X2,sK0)) = X2
      | ~ r2_hidden(X2,k8_filter_1(sK0)) ) ),
    inference(global_subsumption,[],[f159,f211,f212,f355])).

fof(f355,plain,(
    ! [X2] :
      ( k4_tarski(sK3(X2,sK0),sK4(X2,sK0)) = X2
      | ~ r2_hidden(X2,k8_filter_1(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(sK3(X2,sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4(X2,sK0),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f351])).

fof(f351,plain,(
    ! [X2] :
      ( k4_tarski(sK3(X2,sK0),sK4(X2,sK0)) = X2
      | ~ r2_hidden(X2,k8_filter_1(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(sK3(X2,sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK4(X2,sK0),u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f306,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X1)
      | k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_domain_1)).

fof(f306,plain,(
    ! [X2] :
      ( k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(X2,sK0),sK4(X2,sK0)) = X2
      | ~ r2_hidden(X2,k8_filter_1(sK0)) ) ),
    inference(forward_demodulation,[],[f83,f80])).

fof(f80,plain,(
    k8_filter_1(sK0) = a_1_0_filter_1(sK0) ),
    inference(global_subsumption,[],[f40,f39,f70])).

fof(f70,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k8_filter_1(sK0) = a_1_0_filter_1(sK0) ),
    inference(resolution,[],[f38,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | k8_filter_1(X0) = a_1_0_filter_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k8_filter_1(X0) = a_1_0_filter_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_filter_1)).

fof(f39,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,a_1_0_filter_1(sK0))
      | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(X2,sK0),sK4(X2,sK0)) = X2 ) ),
    inference(global_subsumption,[],[f40,f39,f73])).

fof(f73,plain,(
    ! [X2] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK3(X2,sK0),sK4(X2,sK0)) = X2
      | ~ r2_hidden(X2,a_1_0_filter_1(sK0)) ) ),
    inference(resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK3(X0,X1),sK4(X0,X1)) = X0
      | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_1_0_filter_1)).

fof(f212,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(X1,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X1,k8_filter_1(sK0)) ) ),
    inference(forward_demodulation,[],[f82,f80])).

fof(f82,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(X1,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_1_0_filter_1(sK0)) ) ),
    inference(global_subsumption,[],[f40,f39,f72])).

fof(f72,plain,(
    ! [X1] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | m1_subset_1(sK4(X1,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X1,a_1_0_filter_1(sK0)) ) ),
    inference(resolution,[],[f38,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f211,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X0,k8_filter_1(sK0)) ) ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_1_0_filter_1(sK0))
      | m1_subset_1(sK3(X0,sK0),u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f40,f39,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | m1_subset_1(sK3(X0,sK0),u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) ) ),
    inference(resolution,[],[f38,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != k4_tarski(X0,X1)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X2,X3) != k4_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k4_tarski(X0,X1)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(f376,plain,(
    ! [X6,X7] :
      ( r3_lattices(sK0,X6,sK4(k4_tarski(X6,X7),sK0))
      | ~ r2_hidden(k4_tarski(X6,X7),k8_filter_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f368])).

fof(f368,plain,(
    ! [X6,X7] :
      ( r3_lattices(sK0,X6,sK4(k4_tarski(X6,X7),sK0))
      | ~ r2_hidden(k4_tarski(X6,X7),k8_filter_1(sK0))
      | ~ r2_hidden(k4_tarski(X6,X7),k8_filter_1(sK0)) ) ),
    inference(superposition,[],[f251,f364])).

fof(f364,plain,(
    ! [X0,X1] :
      ( sK3(k4_tarski(X0,X1),sK0) = X0
      | ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK0)) ) ),
    inference(equality_resolution,[],[f359])).

fof(f359,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | sK3(X0,sK0) = X1
      | ~ r2_hidden(X0,k8_filter_1(sK0)) ) ),
    inference(superposition,[],[f60,f356])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) != k4_tarski(X0,X1)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f251,plain,(
    ! [X3] :
      ( r3_lattices(sK0,sK3(X3,sK0),sK4(X3,sK0))
      | ~ r2_hidden(X3,k8_filter_1(sK0)) ) ),
    inference(forward_demodulation,[],[f84,f80])).

fof(f84,plain,(
    ! [X3] :
      ( r3_lattices(sK0,sK3(X3,sK0),sK4(X3,sK0))
      | ~ r2_hidden(X3,a_1_0_filter_1(sK0)) ) ),
    inference(global_subsumption,[],[f40,f39,f74])).

fof(f74,plain,(
    ! [X3] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,sK3(X3,sK0),sK4(X3,sK0))
      | ~ r2_hidden(X3,a_1_0_filter_1(sK0)) ) ),
    inference(resolution,[],[f38,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | r3_lattices(X1,sK3(X0,X1),sK4(X0,X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f169,plain,
    ( ~ r3_lattices(sK0,sK1,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f168])).

fof(f348,plain,
    ( ~ spl6_5
    | spl6_6
    | spl6_8
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f345,f164,f336,f312,f308])).

fof(f308,plain,
    ( spl6_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f345,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_1 ),
    inference(superposition,[],[f166,f154])).

fof(f154,plain,(
    ! [X4,X5] :
      ( k1_domain_1(u1_struct_0(sK0),X4,sK1,X5) = k4_tarski(sK1,X5)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X5,X4) ) ),
    inference(global_subsumption,[],[f69,f142,f148])).

fof(f148,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X5,X4)
      | k1_domain_1(u1_struct_0(sK0),X4,sK1,X5) = k4_tarski(sK1,X5) ) ),
    inference(resolution,[],[f37,f62])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f166,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f164])).

fof(f343,plain,
    ( ~ spl6_2
    | ~ spl6_5
    | spl6_8 ),
    inference(avatar_split_clause,[],[f341,f336,f308,f168])).

fof(f341,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r3_lattices(sK0,sK1,sK2)
    | spl6_8 ),
    inference(resolution,[],[f305,f338])).

fof(f338,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f336])).

fof(f305,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1,X0),k8_filter_1(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,sK1,X0) ) ),
    inference(global_subsumption,[],[f38,f39,f40,f37,f159,f304])).

fof(f304,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1,X0),k8_filter_1(sK0))
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,sK1,X0)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f303,f80])).

fof(f303,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1,X0),a_1_0_filter_1(sK0))
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,sK1,X0)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1,X0),a_1_0_filter_1(sK0))
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,sK1,X0)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f63,f154])).

fof(f63,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r3_lattices(X1,X2,X3)
      | r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),a_1_0_filter_1(X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
      | ~ r3_lattices(X1,X2,X3)
      | r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f339,plain,
    ( ~ spl6_5
    | spl6_6
    | ~ spl6_8
    | spl6_1 ),
    inference(avatar_split_clause,[],[f300,f164,f336,f312,f308])).

fof(f300,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl6_1 ),
    inference(superposition,[],[f165,f154])).

fof(f165,plain,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f164])).

fof(f322,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f36,f308])).

fof(f36,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f171,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f34,f168,f164])).

fof(f34,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
