%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 156 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  225 ( 369 expanded)
%              Number of equality atoms :   25 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f60,f65,f88,f93,f106,f122,f134,f147,f157,f189,f265])).

fof(f265,plain,
    ( spl3_16
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl3_16
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f263,f138])).

fof(f138,plain,(
    ! [X0,X1] : r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X1,X0))) ),
    inference(resolution,[],[f53,f24])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f53,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k4_xboole_0(X5,k3_tarski(X3)),k3_tarski(X4))
      | r1_tarski(X5,k3_tarski(k2_xboole_0(X3,X4))) ) ),
    inference(superposition,[],[f31,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f263,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1)))
    | spl3_16
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f262,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f262,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | spl3_16
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f258,f26])).

fof(f258,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2))))
    | spl3_16
    | ~ spl3_22 ),
    inference(superposition,[],[f146,f188])).

fof(f188,plain,
    ( ! [X0] : k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_22
  <=> ! [X0] : k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f146,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_16
  <=> r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f189,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f182,f155,f38,f187])).

fof(f38,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f155,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k3_tarski(k4_xboole_0(X0,X1)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f182,plain,
    ( ! [X0] : k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(resolution,[],[f156,f40])).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k3_tarski(k4_xboole_0(X0,X1)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(X0,X1)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( spl3_17
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f151,f132,f155])).

fof(f132,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k3_tarski(X0) = k5_setfam_1(u1_struct_0(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k3_tarski(k4_xboole_0(X0,X1)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(X0,X1)) )
    | ~ spl3_15 ),
    inference(resolution,[],[f133,f24])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k3_tarski(X0) = k5_setfam_1(u1_struct_0(sK0),X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f147,plain,
    ( ~ spl3_16
    | spl3_13 ),
    inference(avatar_split_clause,[],[f142,f119,f144])).

fof(f119,plain,
    ( spl3_13
  <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f142,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))))
    | spl3_13 ),
    inference(resolution,[],[f121,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f121,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f134,plain,
    ( spl3_15
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f130,f91,f132])).

fof(f91,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X1,X0)
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k3_tarski(X0) = k5_setfam_1(u1_struct_0(sK0),X0) )
    | ~ spl3_10 ),
    inference(resolution,[],[f92,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f92,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f122,plain,
    ( ~ spl3_13
    | ~ spl3_8
    | spl3_9 ),
    inference(avatar_split_clause,[],[f117,f85,f77,f119])).

fof(f77,plain,
    ( spl3_8
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f85,plain,
    ( spl3_9
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f117,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl3_8
    | spl3_9 ),
    inference(subsumption_resolution,[],[f116,f78])).

fof(f78,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f116,plain,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(superposition,[],[f87,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f87,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f106,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f105,f57,f38,f77])).

fof(f57,plain,
    ( spl3_5
  <=> k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f105,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f95,f40])).

fof(f95,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_5 ),
    inference(superposition,[],[f28,f59])).

fof(f59,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f93,plain,
    ( spl3_10
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f89,f33,f91])).

fof(f33,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X1,X0)
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f23,f35])).

fof(f35,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ r1_tarski(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

fof(f88,plain,
    ( ~ spl3_9
    | ~ spl3_2
    | spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f83,f62,f57,f43,f38,f85])).

fof(f43,plain,
    ( spl3_3
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,
    ( spl3_6
  <=> k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f83,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f82,f59])).

fof(f82,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | spl3_3
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f81,f64])).

fof(f64,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f81,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f68,f40])).

fof(f68,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_3 ),
    inference(superposition,[],[f45,f29])).

fof(f45,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f65,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f55,f48,f62])).

fof(f48,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f55,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f27,f50])).

fof(f50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f60,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f54,f38,f57])).

fof(f54,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f27,f40])).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).

fof(f46,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f33])).

fof(f22,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:42:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (16632)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.44  % (16632)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f280,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f60,f65,f88,f93,f106,f122,f134,f147,f157,f189,f265])).
% 0.21/0.44  fof(f265,plain,(
% 0.21/0.44    spl3_16 | ~spl3_22),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f264])).
% 0.21/0.44  fof(f264,plain,(
% 0.21/0.44    $false | (spl3_16 | ~spl3_22)),
% 0.21/0.44    inference(subsumption_resolution,[],[f263,f138])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X1,X0)))) )),
% 0.21/0.44    inference(resolution,[],[f53,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X4,X5,X3] : (~r1_tarski(k4_xboole_0(X5,k3_tarski(X3)),k3_tarski(X4)) | r1_tarski(X5,k3_tarski(k2_xboole_0(X3,X4)))) )),
% 0.21/0.44    inference(superposition,[],[f31,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.21/0.44  fof(f263,plain,(
% 0.21/0.44    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) | (spl3_16 | ~spl3_22)),
% 0.21/0.44    inference(forward_demodulation,[],[f262,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.44  fof(f262,plain,(
% 0.21/0.44    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | (spl3_16 | ~spl3_22)),
% 0.21/0.44    inference(forward_demodulation,[],[f258,f26])).
% 0.21/0.44  fof(f258,plain,(
% 0.21/0.44    ~r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k3_tarski(k4_xboole_0(sK1,sK2)))) | (spl3_16 | ~spl3_22)),
% 0.21/0.44    inference(superposition,[],[f146,f188])).
% 0.21/0.44  fof(f188,plain,(
% 0.21/0.44    ( ! [X0] : (k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))) ) | ~spl3_22),
% 0.21/0.44    inference(avatar_component_clause,[],[f187])).
% 0.21/0.44  fof(f187,plain,(
% 0.21/0.44    spl3_22 <=> ! [X0] : k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.44  fof(f146,plain,(
% 0.21/0.44    ~r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))) | spl3_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f144])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    spl3_16 <=> r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.44  fof(f189,plain,(
% 0.21/0.44    spl3_22 | ~spl3_2 | ~spl3_17),
% 0.21/0.44    inference(avatar_split_clause,[],[f182,f155,f38,f187])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    spl3_17 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k3_tarski(k4_xboole_0(X0,X1)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(X0,X1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.44  fof(f182,plain,(
% 0.21/0.44    ( ! [X0] : (k3_tarski(k4_xboole_0(sK1,X0)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))) ) | (~spl3_2 | ~spl3_17)),
% 0.21/0.44    inference(resolution,[],[f156,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f38])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k3_tarski(k4_xboole_0(X0,X1)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(X0,X1))) ) | ~spl3_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f155])).
% 0.21/0.44  fof(f157,plain,(
% 0.21/0.44    spl3_17 | ~spl3_15),
% 0.21/0.44    inference(avatar_split_clause,[],[f151,f132,f155])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    spl3_15 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k3_tarski(X0) = k5_setfam_1(u1_struct_0(sK0),X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k3_tarski(k4_xboole_0(X0,X1)) = k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(X0,X1))) ) | ~spl3_15),
% 0.21/0.44    inference(resolution,[],[f133,f24])).
% 0.21/0.44  fof(f133,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k3_tarski(X0) = k5_setfam_1(u1_struct_0(sK0),X0)) ) | ~spl3_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f132])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    ~spl3_16 | spl3_13),
% 0.21/0.44    inference(avatar_split_clause,[],[f142,f119,f144])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    spl3_13 <=> r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.44  fof(f142,plain,(
% 0.21/0.44    ~r1_tarski(k3_tarski(sK1),k2_xboole_0(k3_tarski(sK2),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))) | spl3_13),
% 0.21/0.44    inference(resolution,[],[f121,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | spl3_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f119])).
% 0.21/0.44  fof(f134,plain,(
% 0.21/0.44    spl3_15 | ~spl3_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f130,f91,f132])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    spl3_10 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,X0) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k3_tarski(X0) = k5_setfam_1(u1_struct_0(sK0),X0)) ) | ~spl3_10),
% 0.21/0.44    inference(resolution,[],[f92,f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k3_tarski(X1) = k5_setfam_1(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f91])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    ~spl3_13 | ~spl3_8 | spl3_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f117,f85,f77,f119])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl3_8 <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    spl3_9 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | (~spl3_8 | spl3_9)),
% 0.21/0.44    inference(subsumption_resolution,[],[f116,f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f77])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    ~r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 0.21/0.44    inference(superposition,[],[f87,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | spl3_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f85])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl3_8 | ~spl3_2 | ~spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f105,f57,f38,f77])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    spl3_5 <=> k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f95,f40])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_5),
% 0.21/0.44    inference(superposition,[],[f28,f59])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f57])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    spl3_10 | ~spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f89,f33,f91])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    spl3_1 <=> l1_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,X0) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl3_1),
% 0.21/0.44    inference(resolution,[],[f23,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    l1_struct_0(sK0) | ~spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f33])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    ~spl3_9 | ~spl3_2 | spl3_3 | ~spl3_5 | ~spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f83,f62,f57,f43,f38,f85])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    spl3_3 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl3_6 <=> k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | (~spl3_2 | spl3_3 | ~spl3_5 | ~spl3_6)),
% 0.21/0.44    inference(forward_demodulation,[],[f82,f59])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | (~spl3_2 | spl3_3 | ~spl3_6)),
% 0.21/0.44    inference(forward_demodulation,[],[f81,f64])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f62])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | (~spl3_2 | spl3_3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f68,f40])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_3),
% 0.21/0.44    inference(superposition,[],[f45,f29])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) | spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f43])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl3_6 | ~spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f55,f48,f62])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) | ~spl3_4),
% 0.21/0.44    inference(resolution,[],[f27,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f48])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    spl3_5 | ~spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f54,f38,f57])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) | ~spl3_2),
% 0.21/0.44    inference(resolution,[],[f27,f40])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f48])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f10])).
% 0.21/0.44  fof(f10,conjecture,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tops_2)).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f43])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f38])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f33])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    l1_struct_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (16632)------------------------------
% 0.21/0.44  % (16632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (16632)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (16632)Memory used [KB]: 10746
% 0.21/0.44  % (16632)Time elapsed: 0.012 s
% 0.21/0.44  % (16632)------------------------------
% 0.21/0.44  % (16632)------------------------------
% 0.21/0.44  % (16630)Success in time 0.084 s
%------------------------------------------------------------------------------
