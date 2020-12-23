%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:42 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  180 (1947 expanded)
%              Number of leaves         :   25 ( 555 expanded)
%              Depth                    :   33
%              Number of atoms          :  522 (7498 expanded)
%              Number of equality atoms :  118 (1871 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2024,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f89,f96,f103,f106,f124,f1828,f1835,f2023])).

fof(f2023,plain,
    ( spl4_2
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f2022])).

fof(f2022,plain,
    ( $false
    | spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f2021,f87])).

fof(f87,plain,
    ( k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_2
  <=> k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f2021,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f303,f1834])).

fof(f1834,plain,
    ( sK2 = k1_tops_1(sK1,sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f1832])).

fof(f1832,plain,
    ( spl4_9
  <=> sK2 = k1_tops_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f303,plain,(
    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f300,f42])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
      | ~ v3_pre_topc(sK2,sK1) )
    & ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK1,X1) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1)
            | ~ v3_pre_topc(X1,sK1) )
          & ( k2_tops_1(sK1,X1) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1)
            | v3_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK1,X1) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1)
          | ~ v3_pre_topc(X1,sK1) )
        & ( k2_tops_1(sK1,X1) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1)
          | v3_pre_topc(X1,sK1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
        | ~ v3_pre_topc(sK2,sK1) )
      & ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
        | v3_pre_topc(sK2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f300,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f48,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1835,plain,
    ( ~ spl4_1
    | spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1830,f101,f1832,f81])).

fof(f81,plain,
    ( spl4_1
  <=> v3_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f101,plain,
    ( spl4_6
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1830,plain,
    ( sK2 = k1_tops_1(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f184,f42])).

fof(f184,plain,
    ( ~ l1_pre_topc(sK1)
    | sK2 = k1_tops_1(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f102,f43])).

fof(f102,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f1828,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f1827])).

fof(f1827,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1826,f83])).

fof(f83,plain,
    ( ~ v3_pre_topc(sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f1826,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1825,f43])).

fof(f1825,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1824,f42])).

fof(f1824,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f1800,f41])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f1800,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f1799])).

fof(f1799,plain,
    ( sK2 != sK2
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f95,f1770])).

fof(f1770,plain,
    ( sK2 = k1_tops_1(sK1,sK2)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f1158,f1769])).

fof(f1769,plain,
    ( sK2 = k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tops_1(sK1,sK2)))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f1766,f1105])).

fof(f1105,plain,(
    k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = k5_xboole_0(sK2,k1_tops_1(sK1,sK2)) ),
    inference(backward_demodulation,[],[f786,f1033])).

fof(f1033,plain,(
    k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k5_xboole_0(sK2,k1_tops_1(sK1,sK2)) ),
    inference(superposition,[],[f171,f1027])).

fof(f1027,plain,(
    k1_tops_1(sK1,sK2) = k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) ),
    inference(forward_demodulation,[],[f1026,f430])).

fof(f430,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f70,f419])).

fof(f419,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f238,f415])).

fof(f415,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f412,f112])).

fof(f112,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(resolution,[],[f73,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f55,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f412,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2))) ),
    inference(resolution,[],[f410,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2 ) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f53,f52])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f410,plain,(
    ! [X22] : sP0(X22,X22,k1_xboole_0) ),
    inference(global_subsumption,[],[f399])).

fof(f399,plain,(
    ! [X21] : sP0(X21,X21,k1_xboole_0) ),
    inference(resolution,[],[f224,f144])).

fof(f144,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f139,f113])).

fof(f113,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f70,f112])).

fof(f139,plain,(
    ! [X6,X7] : ~ r2_hidden(X6,k5_xboole_0(X7,X7)) ),
    inference(subsumption_resolution,[],[f136,f132])).

fof(f132,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k5_xboole_0(X7,X7))
      | r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f61,f117])).

fof(f117,plain,(
    ! [X4] : sP0(X4,X4,k5_xboole_0(X4,X4)) ),
    inference(superposition,[],[f79,f112])).

fof(f79,plain,(
    ! [X0,X1] : sP0(X1,X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f67,f69])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X0)
              & r2_hidden(sK3(X0,X1,X2),X1) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f136,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k5_xboole_0(X7,X7))
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f62,f117])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f224,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X2,X3] :
      ( sP0(X2,X2,X3)
      | r2_hidden(sK3(X2,X2,X3),X3)
      | r2_hidden(sK3(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(resolution,[],[f65,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f238,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f229,f112])).

fof(f229,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) ),
    inference(superposition,[],[f72,f70])).

fof(f72,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f54,f52,f69,f69])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1026,plain,(
    k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) = k5_xboole_0(k1_tops_1(sK1,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1025,f420])).

fof(f420,plain,(
    ! [X1] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1)) ),
    inference(backward_demodulation,[],[f242,f415])).

fof(f242,plain,(
    ! [X1] : k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f238,f71])).

fof(f71,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f51,f52,f52])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1025,plain,(
    k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(k1_xboole_0,k1_tops_1(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f1021,f71])).

fof(f1021,plain,(
    k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(k1_tops_1(sK1,sK2),k1_xboole_0))) ),
    inference(superposition,[],[f226,f1020])).

fof(f1020,plain,(
    k1_xboole_0 = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f1017,f71])).

fof(f1017,plain,(
    k1_xboole_0 = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(k1_tops_1(sK1,sK2),sK2))) ),
    inference(resolution,[],[f1009,f75])).

fof(f1009,plain,(
    sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1008,f144])).

fof(f1008,plain,
    ( sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0)
    | r2_hidden(sK3(sK2,k1_tops_1(sK1,sK2),k1_xboole_0),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f1007])).

fof(f1007,plain,
    ( sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0)
    | sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0)
    | r2_hidden(sK3(sK2,k1_tops_1(sK1,sK2),k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f831,f65])).

fof(f831,plain,(
    ! [X34] :
      ( r2_hidden(sK3(X34,k1_tops_1(sK1,sK2),k1_xboole_0),sK2)
      | sP0(X34,k1_tops_1(sK1,sK2),k1_xboole_0) ) ),
    inference(resolution,[],[f210,f344])).

fof(f344,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK1,sK2))
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f179,f283])).

fof(f283,plain,(
    k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f280,f42])).

fof(f280,plain,
    ( k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f47,f43])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f179,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k7_subset_1(u1_struct_0(sK1),sK2,X2))
      | r2_hidden(X3,sK2) ) ),
    inference(superposition,[],[f130,f171])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f61,f79])).

fof(f210,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X3,k1_xboole_0),X3)
      | sP0(X2,X3,k1_xboole_0) ) ),
    inference(global_subsumption,[],[f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,k1_xboole_0),X1)
      | sP0(X0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f64,f144])).

fof(f226,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))))) ),
    inference(superposition,[],[f72,f71])).

fof(f171,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK1),sK2,X0) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) ),
    inference(resolution,[],[f74,f43])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f786,plain,(
    k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) ),
    inference(superposition,[],[f240,f283])).

fof(f240,plain,(
    ! [X2] : k1_setfam_1(k2_tarski(sK2,X2)) = k7_subset_1(u1_struct_0(sK1),sK2,k7_subset_1(u1_struct_0(sK1),sK2,X2)) ),
    inference(forward_demodulation,[],[f233,f171])).

fof(f233,plain,(
    ! [X2] : k1_setfam_1(k2_tarski(sK2,X2)) = k7_subset_1(u1_struct_0(sK1),sK2,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X2)))) ),
    inference(superposition,[],[f72,f171])).

fof(f1766,plain,
    ( sK2 = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))))
    | ~ spl4_2 ),
    inference(resolution,[],[f1729,f75])).

fof(f1729,plain,
    ( sP0(k2_tops_1(sK1,sK2),sK2,sK2)
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f1728])).

fof(f1728,plain,
    ( sP0(k2_tops_1(sK1,sK2),sK2,sK2)
    | sP0(k2_tops_1(sK1,sK2),sK2,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f1339,f209])).

fof(f209,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f64])).

fof(f1339,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK3(k2_tops_1(sK1,sK2),X6,X6),sK2)
        | sP0(k2_tops_1(sK1,sK2),X6,X6) )
    | ~ spl4_2 ),
    inference(resolution,[],[f1332,f375])).

fof(f375,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(X1,X2,X2),X1)
      | sP0(X1,X2,X2) ) ),
    inference(subsumption_resolution,[],[f373,f64])).

fof(f373,plain,(
    ! [X2,X1] :
      ( sP0(X1,X2,X2)
      | r2_hidden(sK3(X1,X2,X2),X1)
      | ~ r2_hidden(sK3(X1,X2,X2),X2) ) ),
    inference(duplicate_literal_removal,[],[f357])).

fof(f357,plain,(
    ! [X2,X1] :
      ( sP0(X1,X2,X2)
      | r2_hidden(sK3(X1,X2,X2),X1)
      | ~ r2_hidden(sK3(X1,X2,X2),X2)
      | sP0(X1,X2,X2) ) ),
    inference(resolution,[],[f209,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1332,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tops_1(sK1,sK2))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f1306,f62])).

fof(f1306,plain,
    ( sP0(sK2,k2_pre_topc(sK1,sK2),k2_tops_1(sK1,sK2))
    | ~ spl4_2 ),
    inference(superposition,[],[f1277,f86])).

fof(f86,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f1277,plain,(
    ! [X1] : sP0(X1,k2_pre_topc(sK1,sK2),k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X1)) ),
    inference(superposition,[],[f79,f740])).

fof(f740,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) ),
    inference(subsumption_resolution,[],[f737,f42])).

fof(f737,plain,(
    ! [X0] :
      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f172,f43])).

fof(f172,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3) = k5_xboole_0(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f74,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f1158,plain,(
    k1_tops_1(sK1,sK2) = k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tops_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f350,f1105])).

fof(f350,plain,(
    k1_tops_1(sK1,sK2) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2)))) ),
    inference(resolution,[],[f346,f75])).

fof(f346,plain,(
    sP0(k2_tops_1(sK1,sK2),sK2,k1_tops_1(sK1,sK2)) ),
    inference(superposition,[],[f180,f283])).

fof(f180,plain,(
    ! [X4] : sP0(X4,sK2,k7_subset_1(u1_struct_0(sK1),sK2,X4)) ),
    inference(superposition,[],[f79,f171])).

fof(f95,plain,
    ( ! [X2,X0] :
        ( k1_tops_1(X0,X2) != X2
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X2,X0) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_4
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X2) != X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f124,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f122,f42])).

fof(f122,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f121,f41])).

fof(f121,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f99,f43])).

fof(f99,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_5
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f106,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f104,f42])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f92,f43])).

fof(f92,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_3
  <=> ! [X1,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f103,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f49,f101,f98])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f96,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f50,f94,f91])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f44,f85,f81])).

fof(f44,plain,
    ( k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f45,f85,f81])).

fof(f45,plain,
    ( k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:05:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (31960)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (31952)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (31956)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (31954)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (31951)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (31974)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.54  % (31957)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.54  % (31966)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.32/0.54  % (31953)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.54  % (31961)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.32/0.54  % (31980)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.54  % (31979)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.54  % (31977)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.54  % (31972)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.32/0.54  % (31961)Refutation not found, incomplete strategy% (31961)------------------------------
% 1.32/0.54  % (31961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (31961)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (31961)Memory used [KB]: 10746
% 1.32/0.54  % (31961)Time elapsed: 0.127 s
% 1.32/0.54  % (31961)------------------------------
% 1.32/0.54  % (31961)------------------------------
% 1.32/0.54  % (31979)Refutation not found, incomplete strategy% (31979)------------------------------
% 1.32/0.54  % (31979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (31975)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.54  % (31975)Refutation not found, incomplete strategy% (31975)------------------------------
% 1.32/0.54  % (31975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (31975)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (31975)Memory used [KB]: 10618
% 1.32/0.54  % (31975)Time elapsed: 0.137 s
% 1.32/0.54  % (31975)------------------------------
% 1.32/0.54  % (31975)------------------------------
% 1.32/0.55  % (31967)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.32/0.55  % (31969)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.55  % (31965)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.32/0.55  % (31973)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.32/0.55  % (31971)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.55  % (31976)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.55  % (31962)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.55  % (31968)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.53/0.56  % (31959)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.53/0.56  % (31958)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.53/0.56  % (31964)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.53/0.56  % (31955)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.53/0.56  % (31979)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (31979)Memory used [KB]: 10746
% 1.53/0.56  % (31979)Time elapsed: 0.130 s
% 1.53/0.56  % (31979)------------------------------
% 1.53/0.56  % (31979)------------------------------
% 1.53/0.56  % (31980)Refutation not found, incomplete strategy% (31980)------------------------------
% 1.53/0.56  % (31980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (31980)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (31980)Memory used [KB]: 1663
% 1.53/0.56  % (31980)Time elapsed: 0.003 s
% 1.53/0.56  % (31980)------------------------------
% 1.53/0.56  % (31980)------------------------------
% 1.53/0.56  % (31967)Refutation not found, incomplete strategy% (31967)------------------------------
% 1.53/0.56  % (31967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (31967)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (31967)Memory used [KB]: 10618
% 1.53/0.56  % (31967)Time elapsed: 0.158 s
% 1.53/0.56  % (31967)------------------------------
% 1.53/0.56  % (31967)------------------------------
% 1.53/0.56  % (31970)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.53/0.57  % (31978)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.53/0.58  % (31963)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.53/0.59  % (31978)Refutation not found, incomplete strategy% (31978)------------------------------
% 1.53/0.59  % (31978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (31978)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.59  
% 1.53/0.59  % (31978)Memory used [KB]: 6140
% 1.53/0.59  % (31978)Time elapsed: 0.156 s
% 1.53/0.59  % (31978)------------------------------
% 1.53/0.59  % (31978)------------------------------
% 2.05/0.67  % (31957)Refutation found. Thanks to Tanya!
% 2.05/0.67  % SZS status Theorem for theBenchmark
% 2.05/0.67  % SZS output start Proof for theBenchmark
% 2.05/0.67  fof(f2024,plain,(
% 2.05/0.67    $false),
% 2.05/0.67    inference(avatar_sat_refutation,[],[f88,f89,f96,f103,f106,f124,f1828,f1835,f2023])).
% 2.05/0.67  fof(f2023,plain,(
% 2.05/0.67    spl4_2 | ~spl4_9),
% 2.05/0.67    inference(avatar_contradiction_clause,[],[f2022])).
% 2.05/0.67  fof(f2022,plain,(
% 2.05/0.67    $false | (spl4_2 | ~spl4_9)),
% 2.05/0.67    inference(subsumption_resolution,[],[f2021,f87])).
% 2.05/0.67  fof(f87,plain,(
% 2.05/0.67    k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | spl4_2),
% 2.05/0.67    inference(avatar_component_clause,[],[f85])).
% 2.05/0.67  fof(f85,plain,(
% 2.05/0.67    spl4_2 <=> k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2)),
% 2.05/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.05/0.67  fof(f2021,plain,(
% 2.05/0.67    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~spl4_9),
% 2.05/0.67    inference(forward_demodulation,[],[f303,f1834])).
% 2.05/0.67  fof(f1834,plain,(
% 2.05/0.67    sK2 = k1_tops_1(sK1,sK2) | ~spl4_9),
% 2.05/0.67    inference(avatar_component_clause,[],[f1832])).
% 2.05/0.67  fof(f1832,plain,(
% 2.05/0.67    spl4_9 <=> sK2 = k1_tops_1(sK1,sK2)),
% 2.05/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.05/0.67  fof(f303,plain,(
% 2.05/0.67    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2))),
% 2.05/0.67    inference(subsumption_resolution,[],[f300,f42])).
% 2.05/0.67  fof(f42,plain,(
% 2.05/0.67    l1_pre_topc(sK1)),
% 2.05/0.67    inference(cnf_transformation,[],[f32])).
% 2.05/0.67  fof(f32,plain,(
% 2.05/0.67    ((k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~v3_pre_topc(sK2,sK1)) & (k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.05/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f31,f30])).
% 2.05/0.67  fof(f30,plain,(
% 2.05/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK1,X1) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | ~v3_pre_topc(X1,sK1)) & (k2_tops_1(sK1,X1) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.05/0.67    introduced(choice_axiom,[])).
% 2.05/0.67  fof(f31,plain,(
% 2.05/0.67    ? [X1] : ((k2_tops_1(sK1,X1) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | ~v3_pre_topc(X1,sK1)) & (k2_tops_1(sK1,X1) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X1),X1) | v3_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) => ((k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~v3_pre_topc(sK2,sK1)) & (k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | v3_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 2.05/0.67    introduced(choice_axiom,[])).
% 2.05/0.67  fof(f29,plain,(
% 2.05/0.67    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.05/0.67    inference(flattening,[],[f28])).
% 2.05/0.67  fof(f28,plain,(
% 2.05/0.67    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.05/0.67    inference(nnf_transformation,[],[f17])).
% 2.05/0.67  fof(f17,plain,(
% 2.05/0.67    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.05/0.67    inference(flattening,[],[f16])).
% 2.05/0.67  fof(f16,plain,(
% 2.05/0.67    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.05/0.67    inference(ennf_transformation,[],[f15])).
% 2.05/0.67  fof(f15,negated_conjecture,(
% 2.05/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.05/0.67    inference(negated_conjecture,[],[f14])).
% 2.05/0.67  fof(f14,conjecture,(
% 2.05/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 2.05/0.67  fof(f300,plain,(
% 2.05/0.67    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) | ~l1_pre_topc(sK1)),
% 2.05/0.67    inference(resolution,[],[f48,f43])).
% 2.05/0.67  fof(f43,plain,(
% 2.05/0.67    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.05/0.67    inference(cnf_transformation,[],[f32])).
% 2.05/0.67  fof(f48,plain,(
% 2.05/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f19])).
% 2.05/0.67  fof(f19,plain,(
% 2.05/0.67    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.67    inference(ennf_transformation,[],[f11])).
% 2.05/0.67  fof(f11,axiom,(
% 2.05/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.05/0.67  fof(f1835,plain,(
% 2.05/0.67    ~spl4_1 | spl4_9 | ~spl4_6),
% 2.05/0.67    inference(avatar_split_clause,[],[f1830,f101,f1832,f81])).
% 2.05/0.67  fof(f81,plain,(
% 2.05/0.67    spl4_1 <=> v3_pre_topc(sK2,sK1)),
% 2.05/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.05/0.67  fof(f101,plain,(
% 2.05/0.67    spl4_6 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 2.05/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.05/0.67  fof(f1830,plain,(
% 2.05/0.67    sK2 = k1_tops_1(sK1,sK2) | ~v3_pre_topc(sK2,sK1) | ~spl4_6),
% 2.05/0.67    inference(subsumption_resolution,[],[f184,f42])).
% 2.05/0.67  fof(f184,plain,(
% 2.05/0.67    ~l1_pre_topc(sK1) | sK2 = k1_tops_1(sK1,sK2) | ~v3_pre_topc(sK2,sK1) | ~spl4_6),
% 2.05/0.67    inference(resolution,[],[f102,f43])).
% 2.05/0.67  fof(f102,plain,(
% 2.05/0.67    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl4_6),
% 2.05/0.67    inference(avatar_component_clause,[],[f101])).
% 2.05/0.67  fof(f1828,plain,(
% 2.05/0.67    spl4_1 | ~spl4_2 | ~spl4_4),
% 2.05/0.67    inference(avatar_contradiction_clause,[],[f1827])).
% 2.05/0.67  fof(f1827,plain,(
% 2.05/0.67    $false | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 2.05/0.67    inference(subsumption_resolution,[],[f1826,f83])).
% 2.05/0.67  fof(f83,plain,(
% 2.05/0.67    ~v3_pre_topc(sK2,sK1) | spl4_1),
% 2.05/0.67    inference(avatar_component_clause,[],[f81])).
% 2.05/0.67  fof(f1826,plain,(
% 2.05/0.67    v3_pre_topc(sK2,sK1) | (~spl4_2 | ~spl4_4)),
% 2.05/0.67    inference(subsumption_resolution,[],[f1825,f43])).
% 2.05/0.67  fof(f1825,plain,(
% 2.05/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK2,sK1) | (~spl4_2 | ~spl4_4)),
% 2.05/0.67    inference(subsumption_resolution,[],[f1824,f42])).
% 2.05/0.67  fof(f1824,plain,(
% 2.05/0.67    ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK2,sK1) | (~spl4_2 | ~spl4_4)),
% 2.05/0.67    inference(subsumption_resolution,[],[f1800,f41])).
% 2.05/0.67  fof(f41,plain,(
% 2.05/0.67    v2_pre_topc(sK1)),
% 2.05/0.67    inference(cnf_transformation,[],[f32])).
% 2.05/0.67  fof(f1800,plain,(
% 2.05/0.67    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK2,sK1) | (~spl4_2 | ~spl4_4)),
% 2.05/0.67    inference(trivial_inequality_removal,[],[f1799])).
% 2.05/0.67  fof(f1799,plain,(
% 2.05/0.67    sK2 != sK2 | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(sK2,sK1) | (~spl4_2 | ~spl4_4)),
% 2.05/0.67    inference(superposition,[],[f95,f1770])).
% 2.05/0.67  fof(f1770,plain,(
% 2.05/0.67    sK2 = k1_tops_1(sK1,sK2) | ~spl4_2),
% 2.05/0.67    inference(backward_demodulation,[],[f1158,f1769])).
% 2.05/0.67  fof(f1769,plain,(
% 2.05/0.67    sK2 = k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tops_1(sK1,sK2))) | ~spl4_2),
% 2.05/0.67    inference(forward_demodulation,[],[f1766,f1105])).
% 2.05/0.67  fof(f1105,plain,(
% 2.05/0.67    k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = k5_xboole_0(sK2,k1_tops_1(sK1,sK2))),
% 2.05/0.67    inference(backward_demodulation,[],[f786,f1033])).
% 2.05/0.67  fof(f1033,plain,(
% 2.05/0.67    k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k5_xboole_0(sK2,k1_tops_1(sK1,sK2))),
% 2.05/0.67    inference(superposition,[],[f171,f1027])).
% 2.05/0.67  fof(f1027,plain,(
% 2.05/0.67    k1_tops_1(sK1,sK2) = k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2)))),
% 2.05/0.67    inference(forward_demodulation,[],[f1026,f430])).
% 2.05/0.67  fof(f430,plain,(
% 2.05/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.05/0.67    inference(backward_demodulation,[],[f70,f419])).
% 2.05/0.67  fof(f419,plain,(
% 2.05/0.67    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 2.05/0.67    inference(backward_demodulation,[],[f238,f415])).
% 2.05/0.67  fof(f415,plain,(
% 2.05/0.67    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 2.05/0.67    inference(forward_demodulation,[],[f412,f112])).
% 2.05/0.67  fof(f112,plain,(
% 2.05/0.67    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 2.05/0.67    inference(resolution,[],[f73,f77])).
% 2.05/0.67  fof(f77,plain,(
% 2.05/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.05/0.67    inference(equality_resolution,[],[f58])).
% 2.05/0.67  fof(f58,plain,(
% 2.05/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.05/0.67    inference(cnf_transformation,[],[f34])).
% 2.05/0.67  fof(f34,plain,(
% 2.05/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.67    inference(flattening,[],[f33])).
% 2.05/0.67  fof(f33,plain,(
% 2.05/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.67    inference(nnf_transformation,[],[f3])).
% 2.05/0.67  fof(f3,axiom,(
% 2.05/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.05/0.67  fof(f73,plain,(
% 2.05/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 2.05/0.67    inference(definition_unfolding,[],[f55,f52])).
% 2.05/0.67  fof(f52,plain,(
% 2.05/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.05/0.67    inference(cnf_transformation,[],[f9])).
% 2.05/0.67  fof(f9,axiom,(
% 2.05/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.05/0.67  fof(f55,plain,(
% 2.05/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f22])).
% 2.05/0.67  fof(f22,plain,(
% 2.05/0.67    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.05/0.67    inference(ennf_transformation,[],[f5])).
% 2.05/0.67  fof(f5,axiom,(
% 2.05/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.05/0.67  fof(f412,plain,(
% 2.05/0.67    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X2)))) )),
% 2.05/0.67    inference(resolution,[],[f410,f75])).
% 2.05/0.67  fof(f75,plain,(
% 2.05/0.67    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = X2) )),
% 2.05/0.67    inference(definition_unfolding,[],[f68,f69])).
% 2.05/0.67  fof(f69,plain,(
% 2.05/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.05/0.67    inference(definition_unfolding,[],[f53,f52])).
% 2.05/0.67  fof(f53,plain,(
% 2.05/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.05/0.67    inference(cnf_transformation,[],[f4])).
% 2.05/0.67  fof(f4,axiom,(
% 2.05/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.05/0.67  fof(f68,plain,(
% 2.05/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f40])).
% 2.05/0.67  fof(f40,plain,(
% 2.05/0.67    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.67    inference(nnf_transformation,[],[f27])).
% 2.05/0.67  fof(f27,plain,(
% 2.05/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 2.05/0.67    inference(definition_folding,[],[f2,f26])).
% 2.05/0.67  fof(f26,plain,(
% 2.05/0.67    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.05/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.05/0.67  fof(f2,axiom,(
% 2.05/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.05/0.67  fof(f410,plain,(
% 2.05/0.67    ( ! [X22] : (sP0(X22,X22,k1_xboole_0)) )),
% 2.05/0.67    inference(global_subsumption,[],[f399])).
% 2.05/0.67  fof(f399,plain,(
% 2.05/0.67    ( ! [X21] : (sP0(X21,X21,k1_xboole_0)) )),
% 2.05/0.67    inference(resolution,[],[f224,f144])).
% 2.05/0.67  fof(f144,plain,(
% 2.05/0.67    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.05/0.67    inference(superposition,[],[f139,f113])).
% 2.05/0.67  fof(f113,plain,(
% 2.05/0.67    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.05/0.67    inference(superposition,[],[f70,f112])).
% 2.05/0.67  fof(f139,plain,(
% 2.05/0.67    ( ! [X6,X7] : (~r2_hidden(X6,k5_xboole_0(X7,X7))) )),
% 2.05/0.67    inference(subsumption_resolution,[],[f136,f132])).
% 2.05/0.67  fof(f132,plain,(
% 2.05/0.67    ( ! [X6,X7] : (~r2_hidden(X6,k5_xboole_0(X7,X7)) | r2_hidden(X6,X7)) )),
% 2.05/0.67    inference(resolution,[],[f61,f117])).
% 2.05/0.67  fof(f117,plain,(
% 2.05/0.67    ( ! [X4] : (sP0(X4,X4,k5_xboole_0(X4,X4))) )),
% 2.05/0.67    inference(superposition,[],[f79,f112])).
% 2.05/0.67  fof(f79,plain,(
% 2.05/0.67    ( ! [X0,X1] : (sP0(X1,X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 2.05/0.67    inference(equality_resolution,[],[f76])).
% 2.05/0.67  fof(f76,plain,(
% 2.05/0.67    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 2.05/0.67    inference(definition_unfolding,[],[f67,f69])).
% 2.05/0.67  fof(f67,plain,(
% 2.05/0.67    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.05/0.67    inference(cnf_transformation,[],[f40])).
% 2.05/0.67  fof(f61,plain,(
% 2.05/0.67    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f39])).
% 2.05/0.67  fof(f39,plain,(
% 2.05/0.67    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.05/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 2.05/0.67  fof(f38,plain,(
% 2.05/0.67    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.05/0.67    introduced(choice_axiom,[])).
% 2.05/0.67  fof(f37,plain,(
% 2.05/0.67    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 2.05/0.67    inference(rectify,[],[f36])).
% 2.05/0.67  fof(f36,plain,(
% 2.05/0.67    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.05/0.67    inference(flattening,[],[f35])).
% 2.05/0.67  fof(f35,plain,(
% 2.05/0.67    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 2.05/0.67    inference(nnf_transformation,[],[f26])).
% 2.05/0.67  fof(f136,plain,(
% 2.05/0.67    ( ! [X6,X7] : (~r2_hidden(X6,k5_xboole_0(X7,X7)) | ~r2_hidden(X6,X7)) )),
% 2.05/0.67    inference(resolution,[],[f62,f117])).
% 2.05/0.67  fof(f62,plain,(
% 2.05/0.67    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f39])).
% 2.05/0.67  fof(f224,plain,(
% 2.05/0.67    ( ! [X2,X3] : (r2_hidden(sK3(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 2.05/0.67    inference(duplicate_literal_removal,[],[f223])).
% 2.05/0.67  fof(f223,plain,(
% 2.05/0.67    ( ! [X2,X3] : (sP0(X2,X2,X3) | r2_hidden(sK3(X2,X2,X3),X3) | r2_hidden(sK3(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 2.05/0.67    inference(resolution,[],[f65,f64])).
% 2.05/0.67  fof(f64,plain,(
% 2.05/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f39])).
% 2.05/0.67  fof(f65,plain,(
% 2.05/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | sP0(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f39])).
% 2.05/0.67  fof(f238,plain,(
% 2.05/0.67    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k5_xboole_0(X0,X0)) )),
% 2.05/0.67    inference(forward_demodulation,[],[f229,f112])).
% 2.05/0.67  fof(f229,plain,(
% 2.05/0.67    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))) )),
% 2.05/0.67    inference(superposition,[],[f72,f70])).
% 2.05/0.67  fof(f72,plain,(
% 2.05/0.67    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 2.05/0.67    inference(definition_unfolding,[],[f54,f52,f69,f69])).
% 2.05/0.67  fof(f54,plain,(
% 2.05/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.05/0.67    inference(cnf_transformation,[],[f7])).
% 2.05/0.67  fof(f7,axiom,(
% 2.05/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.05/0.67  fof(f70,plain,(
% 2.05/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 2.05/0.67    inference(definition_unfolding,[],[f46,f69])).
% 2.05/0.67  fof(f46,plain,(
% 2.05/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.05/0.67    inference(cnf_transformation,[],[f6])).
% 2.05/0.67  fof(f6,axiom,(
% 2.05/0.67    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.05/0.67  fof(f1026,plain,(
% 2.05/0.67    k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) = k5_xboole_0(k1_tops_1(sK1,sK2),k1_xboole_0)),
% 2.05/0.67    inference(forward_demodulation,[],[f1025,f420])).
% 2.05/0.67  fof(f420,plain,(
% 2.05/0.67    ( ! [X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1))) )),
% 2.05/0.67    inference(backward_demodulation,[],[f242,f415])).
% 2.05/0.67  fof(f242,plain,(
% 2.05/0.67    ( ! [X1] : (k1_setfam_1(k2_tarski(k1_xboole_0,X1)) = k5_xboole_0(X1,X1)) )),
% 2.05/0.67    inference(superposition,[],[f238,f71])).
% 2.05/0.67  fof(f71,plain,(
% 2.05/0.67    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 2.05/0.67    inference(definition_unfolding,[],[f51,f52,f52])).
% 2.05/0.67  fof(f51,plain,(
% 2.05/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f1])).
% 2.05/0.67  fof(f1,axiom,(
% 2.05/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.05/0.67  fof(f1025,plain,(
% 2.05/0.67    k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(k1_xboole_0,k1_tops_1(sK1,sK2))))),
% 2.05/0.67    inference(forward_demodulation,[],[f1021,f71])).
% 2.05/0.67  fof(f1021,plain,(
% 2.05/0.67    k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))) = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(k1_tops_1(sK1,sK2),k1_xboole_0)))),
% 2.05/0.67    inference(superposition,[],[f226,f1020])).
% 2.05/0.67  fof(f1020,plain,(
% 2.05/0.67    k1_xboole_0 = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(sK2,k1_tops_1(sK1,sK2))))),
% 2.05/0.67    inference(forward_demodulation,[],[f1017,f71])).
% 2.05/0.67  fof(f1017,plain,(
% 2.05/0.67    k1_xboole_0 = k5_xboole_0(k1_tops_1(sK1,sK2),k1_setfam_1(k2_tarski(k1_tops_1(sK1,sK2),sK2)))),
% 2.05/0.67    inference(resolution,[],[f1009,f75])).
% 2.05/0.67  fof(f1009,plain,(
% 2.05/0.67    sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0)),
% 2.05/0.67    inference(subsumption_resolution,[],[f1008,f144])).
% 2.05/0.67  fof(f1008,plain,(
% 2.05/0.67    sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0) | r2_hidden(sK3(sK2,k1_tops_1(sK1,sK2),k1_xboole_0),k1_xboole_0)),
% 2.05/0.67    inference(duplicate_literal_removal,[],[f1007])).
% 2.05/0.67  fof(f1007,plain,(
% 2.05/0.67    sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0) | sP0(sK2,k1_tops_1(sK1,sK2),k1_xboole_0) | r2_hidden(sK3(sK2,k1_tops_1(sK1,sK2),k1_xboole_0),k1_xboole_0)),
% 2.05/0.67    inference(resolution,[],[f831,f65])).
% 2.05/0.67  fof(f831,plain,(
% 2.05/0.67    ( ! [X34] : (r2_hidden(sK3(X34,k1_tops_1(sK1,sK2),k1_xboole_0),sK2) | sP0(X34,k1_tops_1(sK1,sK2),k1_xboole_0)) )),
% 2.05/0.67    inference(resolution,[],[f210,f344])).
% 2.05/0.67  fof(f344,plain,(
% 2.05/0.67    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK1,sK2)) | r2_hidden(X0,sK2)) )),
% 2.05/0.67    inference(superposition,[],[f179,f283])).
% 2.05/0.67  fof(f283,plain,(
% 2.05/0.67    k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2))),
% 2.05/0.67    inference(subsumption_resolution,[],[f280,f42])).
% 2.05/0.67  fof(f280,plain,(
% 2.05/0.67    k1_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) | ~l1_pre_topc(sK1)),
% 2.05/0.67    inference(resolution,[],[f47,f43])).
% 2.05/0.67  fof(f47,plain,(
% 2.05/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f18])).
% 2.05/0.67  fof(f18,plain,(
% 2.05/0.67    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.67    inference(ennf_transformation,[],[f13])).
% 2.05/0.67  fof(f13,axiom,(
% 2.05/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.05/0.67  fof(f179,plain,(
% 2.05/0.67    ( ! [X2,X3] : (~r2_hidden(X3,k7_subset_1(u1_struct_0(sK1),sK2,X2)) | r2_hidden(X3,sK2)) )),
% 2.05/0.67    inference(superposition,[],[f130,f171])).
% 2.05/0.67  fof(f130,plain,(
% 2.05/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) | r2_hidden(X0,X1)) )),
% 2.05/0.67    inference(resolution,[],[f61,f79])).
% 2.05/0.67  fof(f210,plain,(
% 2.05/0.67    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,k1_xboole_0),X3) | sP0(X2,X3,k1_xboole_0)) )),
% 2.05/0.67    inference(global_subsumption,[],[f193])).
% 2.05/0.67  fof(f193,plain,(
% 2.05/0.67    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,k1_xboole_0),X1) | sP0(X0,X1,k1_xboole_0)) )),
% 2.05/0.67    inference(resolution,[],[f64,f144])).
% 2.05/0.67  fof(f226,plain,(
% 2.05/0.67    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))))) )),
% 2.05/0.67    inference(superposition,[],[f72,f71])).
% 2.05/0.67  fof(f171,plain,(
% 2.05/0.67    ( ! [X0] : (k7_subset_1(u1_struct_0(sK1),sK2,X0) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0)))) )),
% 2.05/0.67    inference(resolution,[],[f74,f43])).
% 2.05/0.67  fof(f74,plain,(
% 2.05/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 2.05/0.67    inference(definition_unfolding,[],[f60,f69])).
% 2.05/0.67  fof(f60,plain,(
% 2.05/0.67    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.67    inference(cnf_transformation,[],[f25])).
% 2.05/0.67  fof(f25,plain,(
% 2.05/0.67    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.67    inference(ennf_transformation,[],[f8])).
% 2.05/0.67  fof(f8,axiom,(
% 2.05/0.67    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.05/0.67  fof(f786,plain,(
% 2.05/0.67    k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))) = k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2))),
% 2.05/0.67    inference(superposition,[],[f240,f283])).
% 2.05/0.67  fof(f240,plain,(
% 2.05/0.67    ( ! [X2] : (k1_setfam_1(k2_tarski(sK2,X2)) = k7_subset_1(u1_struct_0(sK1),sK2,k7_subset_1(u1_struct_0(sK1),sK2,X2))) )),
% 2.05/0.67    inference(forward_demodulation,[],[f233,f171])).
% 2.05/0.67  fof(f233,plain,(
% 2.05/0.67    ( ! [X2] : (k1_setfam_1(k2_tarski(sK2,X2)) = k7_subset_1(u1_struct_0(sK1),sK2,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X2))))) )),
% 2.05/0.67    inference(superposition,[],[f72,f171])).
% 2.05/0.67  fof(f1766,plain,(
% 2.05/0.67    sK2 = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2)))) | ~spl4_2),
% 2.05/0.67    inference(resolution,[],[f1729,f75])).
% 2.05/0.67  fof(f1729,plain,(
% 2.05/0.67    sP0(k2_tops_1(sK1,sK2),sK2,sK2) | ~spl4_2),
% 2.05/0.67    inference(duplicate_literal_removal,[],[f1728])).
% 2.05/0.67  fof(f1728,plain,(
% 2.05/0.67    sP0(k2_tops_1(sK1,sK2),sK2,sK2) | sP0(k2_tops_1(sK1,sK2),sK2,sK2) | ~spl4_2),
% 2.05/0.67    inference(resolution,[],[f1339,f209])).
% 2.05/0.67  fof(f209,plain,(
% 2.05/0.67    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 2.05/0.67    inference(factoring,[],[f64])).
% 2.05/0.67  fof(f1339,plain,(
% 2.05/0.67    ( ! [X6] : (~r2_hidden(sK3(k2_tops_1(sK1,sK2),X6,X6),sK2) | sP0(k2_tops_1(sK1,sK2),X6,X6)) ) | ~spl4_2),
% 2.05/0.67    inference(resolution,[],[f1332,f375])).
% 2.05/0.67  fof(f375,plain,(
% 2.05/0.67    ( ! [X2,X1] : (r2_hidden(sK3(X1,X2,X2),X1) | sP0(X1,X2,X2)) )),
% 2.05/0.67    inference(subsumption_resolution,[],[f373,f64])).
% 2.05/0.67  fof(f373,plain,(
% 2.05/0.67    ( ! [X2,X1] : (sP0(X1,X2,X2) | r2_hidden(sK3(X1,X2,X2),X1) | ~r2_hidden(sK3(X1,X2,X2),X2)) )),
% 2.05/0.67    inference(duplicate_literal_removal,[],[f357])).
% 2.05/0.67  fof(f357,plain,(
% 2.05/0.67    ( ! [X2,X1] : (sP0(X1,X2,X2) | r2_hidden(sK3(X1,X2,X2),X1) | ~r2_hidden(sK3(X1,X2,X2),X2) | sP0(X1,X2,X2)) )),
% 2.05/0.67    inference(resolution,[],[f209,f66])).
% 2.05/0.67  fof(f66,plain,(
% 2.05/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f39])).
% 2.05/0.67  fof(f1332,plain,(
% 2.05/0.67    ( ! [X1] : (~r2_hidden(X1,k2_tops_1(sK1,sK2)) | ~r2_hidden(X1,sK2)) ) | ~spl4_2),
% 2.05/0.67    inference(resolution,[],[f1306,f62])).
% 2.05/0.67  fof(f1306,plain,(
% 2.05/0.67    sP0(sK2,k2_pre_topc(sK1,sK2),k2_tops_1(sK1,sK2)) | ~spl4_2),
% 2.05/0.67    inference(superposition,[],[f1277,f86])).
% 2.05/0.67  fof(f86,plain,(
% 2.05/0.67    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~spl4_2),
% 2.05/0.67    inference(avatar_component_clause,[],[f85])).
% 2.05/0.67  fof(f1277,plain,(
% 2.05/0.67    ( ! [X1] : (sP0(X1,k2_pre_topc(sK1,sK2),k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X1))) )),
% 2.05/0.67    inference(superposition,[],[f79,f740])).
% 2.05/0.67  fof(f740,plain,(
% 2.05/0.67    ( ! [X0] : (k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0)))) )),
% 2.05/0.67    inference(subsumption_resolution,[],[f737,f42])).
% 2.05/0.67  fof(f737,plain,(
% 2.05/0.67    ( ! [X0] : (k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),X0) = k5_xboole_0(k2_pre_topc(sK1,sK2),k1_setfam_1(k2_tarski(k2_pre_topc(sK1,sK2),X0))) | ~l1_pre_topc(sK1)) )),
% 2.05/0.67    inference(resolution,[],[f172,f43])).
% 2.05/0.67  fof(f172,plain,(
% 2.05/0.67    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),X3) = k5_xboole_0(k2_pre_topc(X1,X2),k1_setfam_1(k2_tarski(k2_pre_topc(X1,X2),X3))) | ~l1_pre_topc(X1)) )),
% 2.05/0.67    inference(resolution,[],[f74,f56])).
% 2.05/0.67  fof(f56,plain,(
% 2.05/0.67    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f24])).
% 2.05/0.67  fof(f24,plain,(
% 2.05/0.67    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.05/0.67    inference(flattening,[],[f23])).
% 2.05/0.67  fof(f23,plain,(
% 2.05/0.67    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.05/0.67    inference(ennf_transformation,[],[f10])).
% 2.05/0.67  fof(f10,axiom,(
% 2.05/0.67    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.05/0.67  fof(f1158,plain,(
% 2.05/0.67    k1_tops_1(sK1,sK2) = k5_xboole_0(sK2,k5_xboole_0(sK2,k1_tops_1(sK1,sK2)))),
% 2.05/0.67    inference(backward_demodulation,[],[f350,f1105])).
% 2.05/0.67  fof(f350,plain,(
% 2.05/0.67    k1_tops_1(sK1,sK2) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,k2_tops_1(sK1,sK2))))),
% 2.05/0.67    inference(resolution,[],[f346,f75])).
% 2.05/0.67  fof(f346,plain,(
% 2.05/0.67    sP0(k2_tops_1(sK1,sK2),sK2,k1_tops_1(sK1,sK2))),
% 2.05/0.67    inference(superposition,[],[f180,f283])).
% 2.05/0.67  fof(f180,plain,(
% 2.05/0.67    ( ! [X4] : (sP0(X4,sK2,k7_subset_1(u1_struct_0(sK1),sK2,X4))) )),
% 2.05/0.67    inference(superposition,[],[f79,f171])).
% 2.05/0.67  fof(f95,plain,(
% 2.05/0.67    ( ! [X2,X0] : (k1_tops_1(X0,X2) != X2 | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0)) ) | ~spl4_4),
% 2.05/0.67    inference(avatar_component_clause,[],[f94])).
% 2.05/0.67  fof(f94,plain,(
% 2.05/0.67    spl4_4 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2)),
% 2.05/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.05/0.67  fof(f124,plain,(
% 2.05/0.67    ~spl4_5),
% 2.05/0.67    inference(avatar_contradiction_clause,[],[f123])).
% 2.05/0.67  fof(f123,plain,(
% 2.05/0.67    $false | ~spl4_5),
% 2.05/0.67    inference(subsumption_resolution,[],[f122,f42])).
% 2.05/0.67  fof(f122,plain,(
% 2.05/0.67    ~l1_pre_topc(sK1) | ~spl4_5),
% 2.05/0.67    inference(subsumption_resolution,[],[f121,f41])).
% 2.05/0.67  fof(f121,plain,(
% 2.05/0.67    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~spl4_5),
% 2.05/0.67    inference(resolution,[],[f99,f43])).
% 2.05/0.67  fof(f99,plain,(
% 2.05/0.67    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl4_5),
% 2.05/0.67    inference(avatar_component_clause,[],[f98])).
% 2.05/0.67  fof(f98,plain,(
% 2.05/0.67    spl4_5 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.05/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.05/0.67  fof(f106,plain,(
% 2.05/0.67    ~spl4_3),
% 2.05/0.67    inference(avatar_contradiction_clause,[],[f105])).
% 2.05/0.67  fof(f105,plain,(
% 2.05/0.67    $false | ~spl4_3),
% 2.05/0.67    inference(subsumption_resolution,[],[f104,f42])).
% 2.05/0.67  fof(f104,plain,(
% 2.05/0.67    ~l1_pre_topc(sK1) | ~spl4_3),
% 2.05/0.67    inference(resolution,[],[f92,f43])).
% 2.05/0.67  fof(f92,plain,(
% 2.05/0.67    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl4_3),
% 2.05/0.67    inference(avatar_component_clause,[],[f91])).
% 2.05/0.67  fof(f91,plain,(
% 2.05/0.67    spl4_3 <=> ! [X1,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 2.05/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.05/0.67  fof(f103,plain,(
% 2.05/0.67    spl4_5 | spl4_6),
% 2.05/0.67    inference(avatar_split_clause,[],[f49,f101,f98])).
% 2.05/0.67  fof(f49,plain,(
% 2.05/0.67    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f21])).
% 2.05/0.67  fof(f21,plain,(
% 2.05/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.67    inference(flattening,[],[f20])).
% 2.05/0.67  fof(f20,plain,(
% 2.05/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.05/0.67    inference(ennf_transformation,[],[f12])).
% 2.05/0.67  fof(f12,axiom,(
% 2.05/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.05/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 2.05/0.67  fof(f96,plain,(
% 2.05/0.67    spl4_3 | spl4_4),
% 2.05/0.67    inference(avatar_split_clause,[],[f50,f94,f91])).
% 2.05/0.67  fof(f50,plain,(
% 2.05/0.67    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/0.67    inference(cnf_transformation,[],[f21])).
% 2.05/0.67  fof(f89,plain,(
% 2.05/0.67    spl4_1 | spl4_2),
% 2.05/0.67    inference(avatar_split_clause,[],[f44,f85,f81])).
% 2.05/0.67  fof(f44,plain,(
% 2.05/0.67    k2_tops_1(sK1,sK2) = k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | v3_pre_topc(sK2,sK1)),
% 2.05/0.67    inference(cnf_transformation,[],[f32])).
% 2.05/0.67  fof(f88,plain,(
% 2.05/0.67    ~spl4_1 | ~spl4_2),
% 2.05/0.67    inference(avatar_split_clause,[],[f45,f85,f81])).
% 2.05/0.67  fof(f45,plain,(
% 2.05/0.67    k2_tops_1(sK1,sK2) != k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),sK2) | ~v3_pre_topc(sK2,sK1)),
% 2.05/0.67    inference(cnf_transformation,[],[f32])).
% 2.05/0.67  % SZS output end Proof for theBenchmark
% 2.05/0.67  % (31957)------------------------------
% 2.05/0.67  % (31957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.67  % (31957)Termination reason: Refutation
% 2.05/0.67  
% 2.05/0.67  % (31957)Memory used [KB]: 12025
% 2.05/0.67  % (31957)Time elapsed: 0.244 s
% 2.05/0.67  % (31957)------------------------------
% 2.05/0.67  % (31957)------------------------------
% 2.33/0.69  % (31950)Success in time 0.323 s
%------------------------------------------------------------------------------
