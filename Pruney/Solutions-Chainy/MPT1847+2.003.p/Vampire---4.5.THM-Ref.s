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
% DateTime   : Thu Dec  3 13:20:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 394 expanded)
%              Number of leaves         :   17 ( 128 expanded)
%              Depth                    :   26
%              Number of atoms          :  395 (1853 expanded)
%              Number of equality atoms :   51 ( 313 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f110,f301])).

fof(f301,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f299,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v1_tex_2(sK2,sK0)
    & v1_tex_2(sK1,sK0)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tex_2(X2,X0)
                & v1_tex_2(X1,X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,sK0)
              & v1_tex_2(X1,sK0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tex_2(X2,sK0)
            & v1_tex_2(X1,sK0)
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ~ v1_tex_2(X2,sK0)
          & v1_tex_2(sK1,sK0)
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ v1_tex_2(X2,sK0)
        & v1_tex_2(sK1,sK0)
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_pre_topc(X2,sK0) )
   => ( ~ v1_tex_2(sK2,sK0)
      & v1_tex_2(sK1,sK0)
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

fof(f299,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f298,f33])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f298,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f297,f36])).

fof(f36,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f297,plain,
    ( v1_tex_2(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f295,f228])).

fof(f228,plain,
    ( ! [X10] :
        ( ~ v1_subset_1(u1_struct_0(sK1),u1_struct_0(X10))
        | v1_tex_2(sK2,X10)
        | ~ m1_pre_topc(sK2,X10)
        | ~ l1_pre_topc(X10) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f69,f208])).

fof(f208,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f207,f200])).

fof(f200,plain,
    ( u1_struct_0(sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f199,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f199,plain,
    ( u1_struct_0(sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f197,f89])).

fof(f89,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f197,plain,
    ( u1_struct_0(sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(resolution,[],[f196,f37])).

fof(f37,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f196,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK1)
        | u1_struct_0(X1) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X1))) )
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f193,f89])).

fof(f193,plain,
    ( ! [X1] :
        ( u1_struct_0(X1) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,sK1)
        | ~ l1_pre_topc(sK1) )
    | ~ spl4_1 ),
    inference(resolution,[],[f140,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f38,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f140,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X0))) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f139,f34])).

fof(f34,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f139,plain,
    ( ! [X0] :
        ( u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f137,f57])).

fof(f57,plain,
    ( l1_pre_topc(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_1
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f137,plain,
    ( ! [X0] :
        ( u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | ~ l1_pre_topc(sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f74,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f74,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK2)
        | u1_struct_0(X4) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X4))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f70,f57])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(superposition,[],[f52,f47])).

fof(f52,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(X0),u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f207,plain,
    ( u1_struct_0(sK2) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f205,f57])).

fof(f205,plain,
    ( u1_struct_0(sK2) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f201,f37])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(X0))) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f144,f61])).

fof(f61,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_2
  <=> ! [X0] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_pre_topc(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(X0))) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f142,f89])).

fof(f142,plain,
    ( ! [X0] :
        ( u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f111,f46])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(X0))) )
    | ~ spl4_4 ),
    inference(resolution,[],[f89,f70])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f295,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f294,f31])).

fof(f294,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f293,f32])).

fof(f32,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f293,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f292,f35])).

fof(f35,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f292,plain,
    ( v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f291,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f291,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f290,f208])).

fof(f290,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f289,f31])).

fof(f289,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f288,f33])).

fof(f288,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f98,f36])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f43,f44])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f110,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f106,f32])).

fof(f106,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl4_4 ),
    inference(resolution,[],[f105,f31])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) )
    | spl4_4 ),
    inference(resolution,[],[f90,f40])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f67,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f64,f33])).

fof(f64,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl4_1 ),
    inference(resolution,[],[f63,f31])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0) )
    | spl4_1 ),
    inference(resolution,[],[f58,f40])).

fof(f58,plain,
    ( ~ l1_pre_topc(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f62,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f54,f60,f56])).

fof(f54,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f53,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:30:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.48  % (20010)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.49  % (20010)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f302,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f62,f67,f110,f301])).
% 0.20/0.49  fof(f301,plain,(
% 0.20/0.49    ~spl4_1 | ~spl4_2 | ~spl4_4),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f300])).
% 0.20/0.49  fof(f300,plain,(
% 0.20/0.49    $false | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f299,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ((~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24,f23,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(X1,sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ? [X2] : (~v1_tex_2(X2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_pre_topc(X2,sK0)) => (~v1_tex_2(sK2,sK0) & v1_tex_2(sK1,sK0) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f298,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    m1_pre_topc(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f298,plain,(
% 0.20/0.49    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f297,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ~v1_tex_2(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f297,plain,(
% 0.20/0.49    v1_tex_2(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(resolution,[],[f295,f228])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    ( ! [X10] : (~v1_subset_1(u1_struct_0(sK1),u1_struct_0(X10)) | v1_tex_2(sK2,X10) | ~m1_pre_topc(sK2,X10) | ~l1_pre_topc(X10)) ) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(superposition,[],[f69,f208])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    u1_struct_0(sK1) = u1_struct_0(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f207,f200])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    u1_struct_0(sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl4_1 | ~spl4_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f199,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    u1_struct_0(sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(sK1))) | (~spl4_1 | ~spl4_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f197,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    l1_pre_topc(sK1) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl4_4 <=> l1_pre_topc(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    u1_struct_0(sK1) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | (~spl4_1 | ~spl4_4)),
% 0.20/0.49    inference(resolution,[],[f196,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_pre_topc(X1,sK1) | u1_struct_0(X1) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X1)))) ) | (~spl4_1 | ~spl4_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f193,f89])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    ( ! [X1] : (u1_struct_0(X1) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X1))) | ~m1_pre_topc(X1,sK1) | ~l1_pre_topc(sK1)) ) | ~spl4_1),
% 0.20/0.49    inference(resolution,[],[f140,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f38,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X0)))) ) | ~spl4_1),
% 0.20/0.49    inference(forward_demodulation,[],[f139,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X0] : (u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X0))) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ) | ~spl4_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f137,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    l1_pre_topc(sK2) | ~spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl4_1 <=> l1_pre_topc(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ( ! [X0] : (u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X0))) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2)) ) | ~spl4_1),
% 0.20/0.49    inference(resolution,[],[f74,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X4] : (~m1_pre_topc(X4,sK2) | u1_struct_0(X4) = k1_setfam_1(k2_tarski(u1_struct_0(sK2),u1_struct_0(X4)))) ) | ~spl4_1),
% 0.20/0.49    inference(resolution,[],[f70,f57])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X1) | u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_pre_topc(X0,X1)) )),
% 0.20/0.49    inference(superposition,[],[f52,f47])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f41,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.20/0.49    inference(definition_unfolding,[],[f49,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    u1_struct_0(sK2) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f205,f57])).
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    u1_struct_0(sK2) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | (~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(resolution,[],[f201,f37])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK2) | u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(X0)))) ) | (~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(resolution,[],[f144,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK2)) ) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    spl4_2 <=> ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(X0)))) ) | ~spl4_4),
% 0.20/0.49    inference(subsumption_resolution,[],[f142,f89])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X0] : (u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(X0))) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)) ) | ~spl4_4),
% 0.20/0.49    inference(resolution,[],[f111,f46])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK1) | u1_struct_0(X0) = k1_setfam_1(k2_tarski(u1_struct_0(sK1),u1_struct_0(X0)))) ) | ~spl4_4),
% 0.20/0.49    inference(resolution,[],[f89,f70])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(superposition,[],[f45,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_struct_0(X1) = sK3(X0,X1) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(rectify,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f295,plain,(
% 0.20/0.49    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f294,f31])).
% 0.20/0.49  fof(f294,plain,(
% 0.20/0.49    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f293,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f293,plain,(
% 0.20/0.49    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f292,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    v1_tex_2(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f292,plain,(
% 0.20/0.49    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(resolution,[],[f291,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f291,plain,(
% 0.20/0.49    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.49    inference(forward_demodulation,[],[f290,f208])).
% 0.20/0.49  fof(f290,plain,(
% 0.20/0.49    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f289,f31])).
% 0.20/0.49  fof(f289,plain,(
% 0.20/0.49    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f288,f33])).
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(resolution,[],[f98,f36])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(superposition,[],[f43,f44])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    spl4_4),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f109])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    $false | spl4_4),
% 0.20/0.49    inference(subsumption_resolution,[],[f106,f32])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK0) | spl4_4),
% 0.20/0.49    inference(resolution,[],[f105,f31])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0)) ) | spl4_4),
% 0.20/0.49    inference(resolution,[],[f90,f40])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ~l1_pre_topc(sK1) | spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f88])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    spl4_1),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    $false | spl4_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f64,f33])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ~m1_pre_topc(sK2,sK0) | spl4_1),
% 0.20/0.49    inference(resolution,[],[f63,f31])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0)) ) | spl4_1),
% 0.20/0.49    inference(resolution,[],[f58,f40])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ~l1_pre_topc(sK2) | spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f56])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ~spl4_1 | spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f54,f60,f56])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2)) )),
% 0.20/0.49    inference(superposition,[],[f53,f34])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (20010)------------------------------
% 0.20/0.49  % (20010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (20010)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (20010)Memory used [KB]: 10874
% 0.20/0.49  % (20010)Time elapsed: 0.068 s
% 0.20/0.49  % (20010)------------------------------
% 0.20/0.49  % (20010)------------------------------
% 0.20/0.49  % (20006)Success in time 0.141 s
%------------------------------------------------------------------------------
