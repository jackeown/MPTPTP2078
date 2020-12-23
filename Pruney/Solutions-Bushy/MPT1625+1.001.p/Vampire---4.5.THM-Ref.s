%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1625+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 618 expanded)
%              Number of leaves         :   31 ( 200 expanded)
%              Depth                    :   22
%              Number of atoms          :  801 (3468 expanded)
%              Number of equality atoms :   41 ( 193 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f137,f141,f182,f315,f378,f407])).

fof(f407,plain,
    ( spl14_2
    | ~ spl14_4
    | ~ spl14_8 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl14_2
    | ~ spl14_4
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f405,f179])).

fof(f179,plain,
    ( v2_waybel_0(k1_tarski(sK5),sK4)
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl14_8
  <=> v2_waybel_0(k1_tarski(sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f405,plain,
    ( ~ v2_waybel_0(k1_tarski(sK5),sK4)
    | spl14_2
    | ~ spl14_4 ),
    inference(forward_demodulation,[],[f115,f136])).

fof(f136,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl14_4
  <=> k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f115,plain,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4)
    | spl14_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl14_2
  <=> v2_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f378,plain,
    ( spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f374,f104])).

fof(f104,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK12(X0,X1) != X0
            | ~ r2_hidden(sK12(X0,X1),X1) )
          & ( sK12(X0,X1) = X0
            | r2_hidden(sK12(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK12(X0,X1) != X0
          | ~ r2_hidden(sK12(X0,X1),X1) )
        & ( sK12(X0,X1) = X0
          | r2_hidden(sK12(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f374,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(resolution,[],[f369,f147])).

fof(f147,plain,(
    r1_orders_2(sK4,sK5,sK5) ),
    inference(subsumption_resolution,[],[f146,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4)
      | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4) )
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f14,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
              | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK4),X1),sK4)
            | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK4),X1),sK4) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK4),X1),sK4)
          | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK4),X1),sK4) )
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4)
        | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4) )
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
            | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
            | ~ v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
              & v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0)
            & v1_waybel_0(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_waybel_0)).

fof(f146,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f145,f63])).

fof(f63,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f145,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f144,f64])).

fof(f64,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f144,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f143,f65])).

fof(f65,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f143,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f128,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f128,plain,(
    r3_orders_2(sK4,sK5,sK5) ),
    inference(global_subsumption,[],[f122,f127])).

fof(f127,plain,
    ( r3_orders_2(sK4,sK5,sK5)
    | ~ sP13(sK4) ),
    inference(subsumption_resolution,[],[f126,f62])).

fof(f126,plain,
    ( r3_orders_2(sK4,sK5,sK5)
    | v2_struct_0(sK4)
    | ~ sP13(sK4) ),
    inference(subsumption_resolution,[],[f125,f63])).

fof(f125,plain,
    ( r3_orders_2(sK4,sK5,sK5)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ sP13(sK4) ),
    inference(subsumption_resolution,[],[f123,f64])).

fof(f123,plain,
    ( r3_orders_2(sK4,sK5,sK5)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ sP13(sK4) ),
    inference(resolution,[],[f65,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP13(X0) ) ),
    inference(general_splitting,[],[f99,f106_D])).

fof(f106,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP13(X0) ) ),
    inference(cnf_transformation,[],[f106_D])).

% (11632)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f106_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP13(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP13])])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f122,plain,(
    sP13(sK4) ),
    inference(resolution,[],[f65,f106])).

fof(f369,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,k1_tarski(sK5)) )
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f295,f158])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK5))
        | m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl14_3
    | ~ spl14_4 ),
    inference(resolution,[],[f153,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f153,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f152,f131])).

fof(f131,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl14_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl14_3
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f152,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f151,f65])).

fof(f151,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl14_4 ),
    inference(superposition,[],[f94,f136])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f295,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,sK5,X0)
        | ~ r1_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(forward_demodulation,[],[f293,f282])).

fof(f282,plain,
    ( sK5 = sK6(sK4,k1_tarski(sK5))
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(resolution,[],[f196,f105])).

fof(f105,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f196,plain,
    ( r2_hidden(sK6(sK4,k1_tarski(sK5)),k1_tarski(sK5))
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(resolution,[],[f185,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X4] :
              ( ~ r1_orders_2(X0,sK7(X0,X1),X4)
              | ~ r1_orders_2(X0,sK6(X0,X1),X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X1)
          & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_orders_2(X0,X6,sK8(X0,X1,X5,X6))
                  & r1_orders_2(X0,X5,sK8(X0,X1,X5,X6))
                  & r2_hidden(sK8(X0,X1,X5,X6),X1)
                  & m1_subset_1(sK8(X0,X1,X5,X6),u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f44,f47,f46,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  | ~ r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                | ~ r1_orders_2(X0,sK6(X0,X1),X4)
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK6(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              | ~ r1_orders_2(X0,sK6(X0,X1),X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(sK6(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,sK7(X0,X1),X4)
            | ~ r1_orders_2(X0,sK6(X0,X1),X4)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X6,sK8(X0,X1,X5,X6))
        & r1_orders_2(X0,X5,sK8(X0,X1,X5,X6))
        & r2_hidden(sK8(X0,X1,X5,X6),X1)
        & m1_subset_1(sK8(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( r1_orders_2(X0,X6,X7)
                    & r1_orders_2(X0,X5,X7)
                    & r2_hidden(X7,X1)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X3,X4)
                    | ~ r1_orders_2(X0,X2,X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r1_orders_2(X0,X3,X4)
                    & r1_orders_2(X0,X2,X4)
                    & r2_hidden(X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r1_orders_2(X0,X3,X4)
                  & r1_orders_2(X0,X2,X4)
                  & r2_hidden(X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f185,plain,
    ( ~ sP0(sK4,k1_tarski(sK5))
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f184,f150])).

fof(f150,plain,
    ( ~ v1_waybel_0(k1_tarski(sK5),sK4)
    | spl14_1
    | ~ spl14_4 ),
    inference(backward_demodulation,[],[f111,f136])).

fof(f111,plain,
    ( ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl14_1
  <=> v1_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f184,plain,
    ( ~ sP0(sK4,k1_tarski(sK5))
    | v1_waybel_0(k1_tarski(sK5),sK4)
    | spl14_3
    | ~ spl14_4 ),
    inference(resolution,[],[f161,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v1_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_waybel_0(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v1_waybel_0(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ( ( v1_waybel_0(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v1_waybel_0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ( v1_waybel_0(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f161,plain,
    ( sP1(k1_tarski(sK5),sK4)
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f157,f64])).

fof(f157,plain,
    ( sP1(k1_tarski(sK5),sK4)
    | ~ l1_orders_2(sK4)
    | spl14_3
    | ~ spl14_4 ),
    inference(resolution,[],[f153,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f17,f33,f32])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X3,X4)
                                & r1_orders_2(X0,X2,X4)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_0)).

fof(f293,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,sK5,X0)
        | ~ r1_orders_2(sK4,sK6(sK4,k1_tarski(sK5)),X0)
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f292,f185])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,sK5,X0)
        | sP0(sK4,k1_tarski(sK5))
        | ~ r1_orders_2(sK4,sK6(sK4,k1_tarski(sK5)),X0)
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(superposition,[],[f78,f285])).

fof(f285,plain,
    ( sK5 = sK7(sK4,k1_tarski(sK5))
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(resolution,[],[f197,f105])).

fof(f197,plain,
    ( r2_hidden(sK7(sK4,k1_tarski(sK5)),k1_tarski(sK5))
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(resolution,[],[f185,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1),X4)
      | sP0(X0,X1)
      | ~ r1_orders_2(X0,sK6(X0,X1),X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f315,plain,
    ( spl14_3
    | ~ spl14_4
    | spl14_7 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | spl14_3
    | ~ spl14_4
    | spl14_7 ),
    inference(subsumption_resolution,[],[f311,f104])).

fof(f311,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | spl14_3
    | ~ spl14_4
    | spl14_7 ),
    inference(resolution,[],[f310,f147])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,X0,sK5)
        | ~ r2_hidden(X0,k1_tarski(sK5)) )
    | spl14_3
    | ~ spl14_4
    | spl14_7 ),
    inference(subsumption_resolution,[],[f245,f158])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,X0,sK5)
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl14_7 ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,X0,sK5)
        | ~ r1_orders_2(sK4,X0,sK5)
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl14_7 ),
    inference(forward_demodulation,[],[f243,f232])).

fof(f232,plain,
    ( sK5 = sK9(sK4,k1_tarski(sK5))
    | spl14_7 ),
    inference(resolution,[],[f190,f105])).

fof(f190,plain,
    ( r2_hidden(sK9(sK4,k1_tarski(sK5)),k1_tarski(sK5))
    | spl14_7 ),
    inference(resolution,[],[f175,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,sK10(X0,X1))
              | ~ r1_orders_2(X0,X4,sK9(X0,X1))
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X1)
          & m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
          & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ( r1_orders_2(X0,sK11(X0,X1,X5,X6),X6)
                  & r1_orders_2(X0,sK11(X0,X1,X5,X6),X5)
                  & r2_hidden(sK11(X0,X1,X5,X6),X1)
                  & m1_subset_1(sK11(X0,X1,X5,X6),u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f52,f55,f54,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  | ~ r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                | ~ r1_orders_2(X0,X4,sK9(X0,X1))
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK9(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,sK9(X0,X1))
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(sK9(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,X4,sK10(X0,X1))
            | ~ r1_orders_2(X0,X4,sK9(X0,X1))
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X1)
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,sK11(X0,X1,X5,X6),X6)
        & r1_orders_2(X0,sK11(X0,X1,X5,X6),X5)
        & r2_hidden(sK11(X0,X1,X5,X6),X1)
        & m1_subset_1(sK11(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( ! [X6] :
                ( ? [X7] :
                    ( r1_orders_2(X0,X7,X6)
                    & r1_orders_2(X0,X7,X5)
                    & r2_hidden(X7,X1)
                    & m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    | ~ r1_orders_2(X0,X4,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( r1_orders_2(X0,X4,X3)
                    & r1_orders_2(X0,X4,X2)
                    & r2_hidden(X4,X1)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X2)
                  & r2_hidden(X4,X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f175,plain,
    ( ~ sP2(sK4,k1_tarski(sK5))
    | spl14_7 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl14_7
  <=> sP2(sK4,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,X0,sK5)
        | ~ r1_orders_2(sK4,X0,sK9(sK4,k1_tarski(sK5)))
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl14_7 ),
    inference(subsumption_resolution,[],[f242,f175])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK4,X0,sK5)
        | sP2(sK4,k1_tarski(sK5))
        | ~ r1_orders_2(sK4,X0,sK9(sK4,k1_tarski(sK5)))
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl14_7 ),
    inference(superposition,[],[f90,f235])).

fof(f235,plain,
    ( sK5 = sK10(sK4,k1_tarski(sK5))
    | spl14_7 ),
    inference(resolution,[],[f191,f105])).

fof(f191,plain,
    ( r2_hidden(sK10(sK4,k1_tarski(sK5)),k1_tarski(sK5))
    | spl14_7 ),
    inference(resolution,[],[f175,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | r2_hidden(sK10(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_orders_2(X0,X4,sK10(X0,X1))
      | sP2(X0,X1)
      | ~ r1_orders_2(X0,X4,sK9(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f182,plain,
    ( spl14_8
    | ~ spl14_7
    | spl14_3
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f172,f134,f130,f174,f178])).

fof(f172,plain,
    ( ~ sP2(sK4,k1_tarski(sK5))
    | v2_waybel_0(k1_tarski(sK5),sK4)
    | spl14_3
    | ~ spl14_4 ),
    inference(resolution,[],[f160,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | ~ sP2(X1,X0)
      | v2_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_waybel_0(X0,X1)
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ~ v2_waybel_0(X0,X1) ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ( ( v2_waybel_0(X1,X0)
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | ~ v2_waybel_0(X1,X0) ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( v2_waybel_0(X1,X0)
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f160,plain,
    ( sP3(k1_tarski(sK5),sK4)
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f156,f64])).

fof(f156,plain,
    ( sP3(k1_tarski(sK5),sK4)
    | ~ l1_orders_2(sK4)
    | spl14_3
    | ~ spl14_4 ),
    inference(resolution,[],[f153,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP3(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f19,f36,f35])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X4,X3)
                                & r1_orders_2(X0,X4,X2)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_0)).

fof(f141,plain,(
    ~ spl14_3 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f139,f62])).

fof(f139,plain,
    ( v2_struct_0(sK4)
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f138,f117])).

fof(f117,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f64,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f138,plain,
    ( ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ spl14_3 ),
    inference(resolution,[],[f132,f92])).

fof(f92,plain,(
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

fof(f132,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f137,plain,
    ( spl14_3
    | spl14_4 ),
    inference(avatar_split_clause,[],[f124,f134,f130])).

fof(f124,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f65,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f116,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f66,f113,f109])).

fof(f66,plain,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4)
    | ~ v1_waybel_0(k6_domain_1(u1_struct_0(sK4),sK5),sK4) ),
    inference(cnf_transformation,[],[f40])).

%------------------------------------------------------------------------------
