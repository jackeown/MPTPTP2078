%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  194 (1490 expanded)
%              Number of leaves         :   30 ( 623 expanded)
%              Depth                    :   28
%              Number of atoms          :  669 (8932 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f793,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f184,f193,f210,f220,f385,f437,f465,f478,f522,f792])).

fof(f792,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f791])).

fof(f791,plain,
    ( $false
    | spl7_10 ),
    inference(subsumption_resolution,[],[f790,f64])).

fof(f64,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f47,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,sK3)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3))) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,sK3)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3))) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(sK2,sK3)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3))) )
      & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(sK2,sK3)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3))) )
   => ( ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))
      & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f790,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl7_10 ),
    inference(resolution,[],[f737,f209])).

fof(f209,plain,
    ( ~ sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl7_10
  <=> sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f737,plain,(
    ! [X1] :
      ( sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f736,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f736,plain,(
    ! [X1] :
      ( sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f735,f62])).

fof(f62,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f735,plain,(
    ! [X1] :
      ( sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f726,f63])).

fof(f63,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f726,plain,(
    ! [X1] :
      ( sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f717,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f42,f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( sP0(X0,X2,X1)
    <=> ( v3_pre_topc(X2,X0)
        & r2_hidden(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f42,plain,(
    ! [X1,X2,X0] :
      ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f717,plain,(
    m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f716,f333])).

fof(f333,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f332,f61])).

fof(f332,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f331,f62])).

fof(f331,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f330,f63])).

fof(f330,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f329,f64])).

fof(f329,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f324,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f324,plain,(
    m1_connsp_2(sK4,sK2,sK3) ),
    inference(subsumption_resolution,[],[f323,f61])).

fof(f323,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f322,f62])).

fof(f322,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f321,f63])).

fof(f321,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f316,f64])).

fof(f316,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f74,f65])).

fof(f65,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f716,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f710,f338])).

fof(f338,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f337,f61])).

fof(f337,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f336,f62])).

fof(f336,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f335,f63])).

fof(f335,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f334,f64])).

fof(f334,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f328,f85])).

fof(f328,plain,(
    m1_connsp_2(sK5,sK2,sK3) ),
    inference(subsumption_resolution,[],[f327,f61])).

fof(f327,plain,
    ( m1_connsp_2(sK5,sK2,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f326,f62])).

fof(f326,plain,
    ( m1_connsp_2(sK5,sK2,sK3)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f325,f63])).

fof(f325,plain,
    ( m1_connsp_2(sK5,sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f317,f64])).

fof(f317,plain,
    ( m1_connsp_2(sK5,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f74,f66])).

fof(f66,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f48])).

fof(f710,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(superposition,[],[f89,f701])).

fof(f701,plain,(
    k3_tarski(k2_tarski(sK4,sK5)) = k4_subset_1(u1_struct_0(sK2),sK4,sK5) ),
    inference(resolution,[],[f350,f333])).

fof(f350,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | k4_subset_1(u1_struct_0(sK2),X2,sK5) = k3_tarski(k2_tarski(X2,sK5)) ) ),
    inference(resolution,[],[f338,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f90,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f522,plain,
    ( ~ spl7_6
    | ~ spl7_8
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f521])).

fof(f521,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_8
    | spl7_12 ),
    inference(subsumption_resolution,[],[f520,f62])).

fof(f520,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ spl7_6
    | ~ spl7_8
    | spl7_12 ),
    inference(subsumption_resolution,[],[f519,f63])).

fof(f519,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_6
    | ~ spl7_8
    | spl7_12 ),
    inference(subsumption_resolution,[],[f518,f394])).

fof(f394,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f183,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ v3_pre_topc(X1,X0)
        | ~ r2_hidden(X2,X1) )
      & ( ( v3_pre_topc(X1,X0)
          & r2_hidden(X2,X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ~ v3_pre_topc(X2,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( v3_pre_topc(X2,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ~ v3_pre_topc(X2,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( v3_pre_topc(X2,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f183,plain,
    ( sP0(sK2,sK4,sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_6
  <=> sP0(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f518,plain,
    ( ~ v3_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_8
    | spl7_12 ),
    inference(subsumption_resolution,[],[f517,f333])).

fof(f517,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_8
    | spl7_12 ),
    inference(subsumption_resolution,[],[f516,f475])).

fof(f475,plain,
    ( v3_pre_topc(sK5,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f192,f71])).

fof(f192,plain,
    ( sP0(sK2,sK5,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl7_8
  <=> sP0(sK2,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f516,plain,
    ( ~ v3_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl7_12 ),
    inference(subsumption_resolution,[],[f515,f338])).

fof(f515,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl7_12 ),
    inference(resolution,[],[f219,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f87,f78])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

% (9582)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f219,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl7_12
  <=> v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f478,plain,
    ( ~ spl7_8
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | ~ spl7_8
    | spl7_11 ),
    inference(subsumption_resolution,[],[f476,f221])).

fof(f221,plain,
    ( ~ r2_hidden(sK3,sK5)
    | spl7_11 ),
    inference(resolution,[],[f215,f158])).

fof(f158,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X6,k3_tarski(k2_tarski(X8,X7)))
      | ~ r2_hidden(X6,X7) ) ),
    inference(subsumption_resolution,[],[f157,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f157,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,X7)
      | r2_hidden(X6,k3_tarski(k2_tarski(X8,X7)))
      | v1_xboole_0(X7) ) ),
    inference(resolution,[],[f149,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X2)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(resolution,[],[f141,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_tarski(k2_tarski(X3,X2))) ) ),
    inference(resolution,[],[f95,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f86,f78])).

% (9576)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f215,plain,
    ( ~ r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5)))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_11
  <=> r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f476,plain,
    ( r2_hidden(sK3,sK5)
    | ~ spl7_8 ),
    inference(resolution,[],[f192,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f465,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f463,f121])).

fof(f121,plain,
    ( v1_xboole_0(sK4)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_4
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f463,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(resolution,[],[f456,f76])).

fof(f456,plain,(
    r2_hidden(sK3,sK4) ),
    inference(subsumption_resolution,[],[f455,f64])).

fof(f455,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[],[f411,f324])).

fof(f411,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(sK4,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_hidden(X4,sK4) ) ),
    inference(subsumption_resolution,[],[f410,f61])).

fof(f410,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(sK4,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_hidden(X4,sK4)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f409,f62])).

fof(f409,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(sK4,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_hidden(X4,sK4)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f404,f63])).

fof(f404,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(sK4,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_hidden(X4,sK4)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f75,f333])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f437,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f432,f188])).

fof(f188,plain,
    ( ~ sP1(sK3,sK5,sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl7_7
  <=> sP1(sK3,sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f432,plain,(
    sP1(sK3,sK5,sK2) ),
    inference(resolution,[],[f356,f64])).

fof(f356,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X0,sK5,sK2) ) ),
    inference(subsumption_resolution,[],[f355,f61])).

fof(f355,plain,(
    ! [X0] :
      ( sP1(X0,sK5,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f354,f62])).

fof(f354,plain,(
    ! [X0] :
      ( sP1(X0,sK5,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f348,f63])).

fof(f348,plain,(
    ! [X0] :
      ( sP1(X0,sK5,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f338,f73])).

fof(f385,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f380,f179])).

fof(f179,plain,
    ( ~ sP1(sK3,sK4,sK2)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl7_5
  <=> sP1(sK3,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f380,plain,(
    sP1(sK3,sK4,sK2) ),
    inference(resolution,[],[f347,f64])).

fof(f347,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X0,sK4,sK2) ) ),
    inference(subsumption_resolution,[],[f346,f61])).

fof(f346,plain,(
    ! [X0] :
      ( sP1(X0,sK4,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f345,f62])).

fof(f345,plain,(
    ! [X0] :
      ( sP1(X0,sK4,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f339,f63])).

fof(f339,plain,(
    ! [X0] :
      ( sP1(X0,sK4,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f333,f73])).

fof(f220,plain,
    ( ~ spl7_11
    | ~ spl7_12
    | spl7_9 ),
    inference(avatar_split_clause,[],[f211,f203,f217,f213])).

fof(f203,plain,
    ( spl7_9
  <=> sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f211,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2)
    | ~ r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5)))
    | spl7_9 ),
    inference(resolution,[],[f205,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f205,plain,
    ( ~ sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f203])).

fof(f210,plain,
    ( ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f201,f207,f203])).

fof(f201,plain,
    ( ~ sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2)
    | ~ sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3) ),
    inference(resolution,[],[f196,f94])).

fof(f94,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(definition_unfolding,[],[f67,f78])).

fof(f67,plain,(
    ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f48])).

fof(f196,plain,(
    ! [X10,X8,X9] :
      ( m1_subset_1(X9,u1_struct_0(k9_yellow_6(X8,X10)))
      | ~ sP1(X10,X9,X8)
      | ~ sP0(X8,X9,X10) ) ),
    inference(resolution,[],[f69,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f80,f76])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X2,X0] :
      ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f193,plain,
    ( ~ spl7_7
    | spl7_8
    | spl7_3 ),
    inference(avatar_split_clause,[],[f174,f115,f190,f186])).

fof(f115,plain,
    ( spl7_3
  <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f174,plain,
    ( sP0(sK2,sK5,sK3)
    | ~ sP1(sK3,sK5,sK2)
    | spl7_3 ),
    inference(resolution,[],[f68,f133])).

fof(f133,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | spl7_3 ),
    inference(subsumption_resolution,[],[f127,f117])).

fof(f117,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f127,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[],[f79,f66])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f184,plain,
    ( ~ spl7_5
    | spl7_6
    | spl7_3 ),
    inference(avatar_split_clause,[],[f173,f115,f181,f177])).

fof(f173,plain,
    ( sP0(sK2,sK4,sK3)
    | ~ sP1(sK3,sK4,sK2)
    | spl7_3 ),
    inference(resolution,[],[f68,f132])).

fof(f132,plain,
    ( r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | spl7_3 ),
    inference(subsumption_resolution,[],[f126,f117])).

fof(f126,plain,
    ( r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[],[f79,f65])).

fof(f122,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f102,f119,f115])).

fof(f102,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[],[f81,f65])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:50:09 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.45  % (9581)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (9575)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (9583)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (9581)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f793,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f122,f184,f193,f210,f220,f385,f437,f465,f478,f522,f792])).
% 0.21/0.48  fof(f792,plain,(
% 0.21/0.48    spl7_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f791])).
% 0.21/0.48  fof(f791,plain,(
% 0.21/0.48    $false | spl7_10),
% 0.21/0.48    inference(subsumption_resolution,[],[f790,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    (((~m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f47,f46,f45,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ? [X3] : (~m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3)))) => (~m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f16])).
% 0.21/0.48  fof(f16,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).
% 0.21/0.48  fof(f790,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl7_10),
% 0.21/0.48    inference(resolution,[],[f737,f209])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ~sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2) | spl7_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f207])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    spl7_10 <=> sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.48  fof(f737,plain,(
% 0.21/0.48    ( ! [X1] : (sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~m1_subset_1(X1,u1_struct_0(sK2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f736,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f736,plain,(
% 0.21/0.48    ( ! [X1] : (sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f735,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    v2_pre_topc(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f735,plain,(
% 0.21/0.48    ( ! [X1] : (sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f726,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    l1_pre_topc(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f726,plain,(
% 0.21/0.48    ( ! [X1] : (sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f717,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X1,X2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (sP1(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(definition_folding,[],[f21,f42,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X1,X2,X0] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).
% 0.21/0.48  fof(f717,plain,(
% 0.21/0.48    m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f716,f333])).
% 0.21/0.48  fof(f333,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f332,f61])).
% 0.21/0.48  fof(f332,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f331,f62])).
% 0.21/0.48  fof(f331,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f330,f63])).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f329,f64])).
% 0.21/0.48  fof(f329,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f324,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    m1_connsp_2(sK4,sK2,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f323,f61])).
% 0.21/0.48  fof(f323,plain,(
% 0.21/0.48    m1_connsp_2(sK4,sK2,sK3) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f322,f62])).
% 0.21/0.48  fof(f322,plain,(
% 0.21/0.48    m1_connsp_2(sK4,sK2,sK3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f321,f63])).
% 0.21/0.48  fof(f321,plain,(
% 0.21/0.48    m1_connsp_2(sK4,sK2,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f316,f64])).
% 0.21/0.48  fof(f316,plain,(
% 0.21/0.48    m1_connsp_2(sK4,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f74,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).
% 0.21/0.48  fof(f716,plain,(
% 0.21/0.48    m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f710,f338])).
% 0.21/0.48  fof(f338,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f337,f61])).
% 0.21/0.48  fof(f337,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f336,f62])).
% 0.21/0.48  fof(f336,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f335,f63])).
% 0.21/0.48  fof(f335,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f334,f64])).
% 0.21/0.48  fof(f334,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f328,f85])).
% 0.21/0.48  fof(f328,plain,(
% 0.21/0.48    m1_connsp_2(sK5,sK2,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f327,f61])).
% 0.21/0.48  fof(f327,plain,(
% 0.21/0.48    m1_connsp_2(sK5,sK2,sK3) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f326,f62])).
% 0.21/0.48  fof(f326,plain,(
% 0.21/0.48    m1_connsp_2(sK5,sK2,sK3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f325,f63])).
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    m1_connsp_2(sK5,sK2,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f317,f64])).
% 0.21/0.48  fof(f317,plain,(
% 0.21/0.48    m1_connsp_2(sK5,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f74,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f710,plain,(
% 0.21/0.48    m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    inference(superposition,[],[f89,f701])).
% 0.21/0.48  fof(f701,plain,(
% 0.21/0.48    k3_tarski(k2_tarski(sK4,sK5)) = k4_subset_1(u1_struct_0(sK2),sK4,sK5)),
% 0.21/0.48    inference(resolution,[],[f350,f333])).
% 0.21/0.48  fof(f350,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | k4_subset_1(u1_struct_0(sK2),X2,sK5) = k3_tarski(k2_tarski(X2,sK5))) )),
% 0.21/0.48    inference(resolution,[],[f338,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f90,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.21/0.48  fof(f522,plain,(
% 0.21/0.48    ~spl7_6 | ~spl7_8 | spl7_12),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f521])).
% 0.21/0.48  fof(f521,plain,(
% 0.21/0.48    $false | (~spl7_6 | ~spl7_8 | spl7_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f520,f62])).
% 0.21/0.48  fof(f520,plain,(
% 0.21/0.48    ~v2_pre_topc(sK2) | (~spl7_6 | ~spl7_8 | spl7_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f519,f63])).
% 0.21/0.48  fof(f519,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl7_6 | ~spl7_8 | spl7_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f518,f394])).
% 0.21/0.48  fof(f394,plain,(
% 0.21/0.48    v3_pre_topc(sK4,sK2) | ~spl7_6),
% 0.21/0.48    inference(resolution,[],[f183,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v3_pre_topc(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1)) & ((v3_pre_topc(X1,X0) & r2_hidden(X2,X1)) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(rectify,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X2,X1)))),
% 0.21/0.48    inference(flattening,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X2,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f41])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    sP0(sK2,sK4,sK3) | ~spl7_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f181])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    spl7_6 <=> sP0(sK2,sK4,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.48  fof(f518,plain,(
% 0.21/0.48    ~v3_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl7_8 | spl7_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f517,f333])).
% 0.21/0.48  fof(f517,plain,(
% 0.21/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl7_8 | spl7_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f516,f475])).
% 0.21/0.48  fof(f475,plain,(
% 0.21/0.48    v3_pre_topc(sK5,sK2) | ~spl7_8),
% 0.21/0.48    inference(resolution,[],[f192,f71])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    sP0(sK2,sK5,sK3) | ~spl7_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f190])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    spl7_8 <=> sP0(sK2,sK5,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.48  fof(f516,plain,(
% 0.21/0.48    ~v3_pre_topc(sK5,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl7_12),
% 0.21/0.48    inference(subsumption_resolution,[],[f515,f338])).
% 0.21/0.48  fof(f515,plain,(
% 0.21/0.48    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK5,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl7_12),
% 0.21/0.48    inference(resolution,[],[f219,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f87,f78])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f33])).
% 0.21/0.48  % (9582)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ~v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2) | spl7_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f217])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    spl7_12 <=> v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.48  fof(f478,plain,(
% 0.21/0.48    ~spl7_8 | spl7_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f477])).
% 0.21/0.48  fof(f477,plain,(
% 0.21/0.48    $false | (~spl7_8 | spl7_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f476,f221])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    ~r2_hidden(sK3,sK5) | spl7_11),
% 0.21/0.48    inference(resolution,[],[f215,f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ( ! [X6,X8,X7] : (r2_hidden(X6,k3_tarski(k2_tarski(X8,X7))) | ~r2_hidden(X6,X7)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f157,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f55,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(rectify,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ( ! [X6,X8,X7] : (~r2_hidden(X6,X7) | r2_hidden(X6,k3_tarski(k2_tarski(X8,X7))) | v1_xboole_0(X7)) )),
% 0.21/0.48    inference(resolution,[],[f149,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f57])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X2) | ~r2_hidden(X0,X2) | r2_hidden(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 0.21/0.48    inference(resolution,[],[f141,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.48    inference(flattening,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.48    inference(nnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,k3_tarski(k2_tarski(X3,X2)))) )),
% 0.21/0.48    inference(resolution,[],[f95,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f60])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f86,f78])).
% 0.21/0.48  % (9576)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5))) | spl7_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f213])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    spl7_11 <=> r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.48  fof(f476,plain,(
% 0.21/0.48    r2_hidden(sK3,sK5) | ~spl7_8),
% 0.21/0.48    inference(resolution,[],[f192,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f465,plain,(
% 0.21/0.48    ~spl7_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f464])).
% 0.21/0.48  fof(f464,plain,(
% 0.21/0.48    $false | ~spl7_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f463,f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    v1_xboole_0(sK4) | ~spl7_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl7_4 <=> v1_xboole_0(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.48  fof(f463,plain,(
% 0.21/0.48    ~v1_xboole_0(sK4)),
% 0.21/0.48    inference(resolution,[],[f456,f76])).
% 0.21/0.48  fof(f456,plain,(
% 0.21/0.48    r2_hidden(sK3,sK4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f455,f64])).
% 0.21/0.48  fof(f455,plain,(
% 0.21/0.48    ~m1_subset_1(sK3,u1_struct_0(sK2)) | r2_hidden(sK3,sK4)),
% 0.21/0.48    inference(resolution,[],[f411,f324])).
% 0.21/0.48  fof(f411,plain,(
% 0.21/0.48    ( ! [X4] : (~m1_connsp_2(sK4,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK2)) | r2_hidden(X4,sK4)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f410,f61])).
% 0.21/0.48  fof(f410,plain,(
% 0.21/0.48    ( ! [X4] : (~m1_connsp_2(sK4,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK2)) | r2_hidden(X4,sK4) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f409,f62])).
% 0.21/0.48  fof(f409,plain,(
% 0.21/0.48    ( ! [X4] : (~m1_connsp_2(sK4,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK2)) | r2_hidden(X4,sK4) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f404,f63])).
% 0.21/0.48  fof(f404,plain,(
% 0.21/0.48    ( ! [X4] : (~m1_connsp_2(sK4,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK2)) | r2_hidden(X4,sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f75,f333])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.21/0.48  fof(f437,plain,(
% 0.21/0.48    spl7_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f436])).
% 0.21/0.48  fof(f436,plain,(
% 0.21/0.48    $false | spl7_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f432,f188])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK2) | spl7_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    spl7_7 <=> sP1(sK3,sK5,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.48  fof(f432,plain,(
% 0.21/0.48    sP1(sK3,sK5,sK2)),
% 0.21/0.48    inference(resolution,[],[f356,f64])).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | sP1(X0,sK5,sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f355,f61])).
% 0.21/0.48  fof(f355,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(X0,sK5,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f354,f62])).
% 0.21/0.48  fof(f354,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(X0,sK5,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f348,f63])).
% 0.21/0.48  fof(f348,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(X0,sK5,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f338,f73])).
% 0.21/0.48  fof(f385,plain,(
% 0.21/0.48    spl7_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f384])).
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    $false | spl7_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f380,f179])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    ~sP1(sK3,sK4,sK2) | spl7_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f177])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    spl7_5 <=> sP1(sK3,sK4,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    sP1(sK3,sK4,sK2)),
% 0.21/0.48    inference(resolution,[],[f347,f64])).
% 0.21/0.48  fof(f347,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | sP1(X0,sK4,sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f346,f61])).
% 0.21/0.48  fof(f346,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(X0,sK4,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f345,f62])).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(X0,sK4,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f339,f63])).
% 0.21/0.48  fof(f339,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(X0,sK4,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f333,f73])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ~spl7_11 | ~spl7_12 | spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f211,f203,f217,f213])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    spl7_9 <=> sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    ~v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5))) | spl7_9),
% 0.21/0.48    inference(resolution,[],[f205,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    ~sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3) | spl7_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f203])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    ~spl7_9 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f201,f207,f203])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    ~sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3)),
% 0.21/0.48    inference(resolution,[],[f196,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ~m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.21/0.48    inference(definition_unfolding,[],[f67,f78])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    ( ! [X10,X8,X9] : (m1_subset_1(X9,u1_struct_0(k9_yellow_6(X8,X10))) | ~sP1(X10,X9,X8) | ~sP0(X8,X9,X10)) )),
% 0.21/0.48    inference(resolution,[],[f69,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f80,f76])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))))) | ~sP1(X0,X1,X2))),
% 0.21/0.48    inference(rectify,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ! [X1,X2,X0] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~sP1(X1,X2,X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f42])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ~spl7_7 | spl7_8 | spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f174,f115,f190,f186])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl7_3 <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    sP0(sK2,sK5,sK3) | ~sP1(sK3,sK5,sK2) | spl7_3),
% 0.21/0.48    inference(resolution,[],[f68,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) | spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f115])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.21/0.48    inference(resolution,[],[f79,f66])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f58])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f50])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    ~spl7_5 | spl7_6 | spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f173,f115,f181,f177])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    sP0(sK2,sK4,sK3) | ~sP1(sK3,sK4,sK2) | spl7_3),
% 0.21/0.48    inference(resolution,[],[f68,f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f126,f117])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.21/0.48    inference(resolution,[],[f79,f65])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ~spl7_3 | spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f102,f119,f115])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    v1_xboole_0(sK4) | ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.21/0.48    inference(resolution,[],[f81,f65])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f58])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9581)------------------------------
% 0.21/0.48  % (9581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9581)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9581)Memory used [KB]: 11257
% 0.21/0.48  % (9581)Time elapsed: 0.034 s
% 0.21/0.48  % (9581)------------------------------
% 0.21/0.48  % (9581)------------------------------
% 0.21/0.49  % (9571)Success in time 0.128 s
%------------------------------------------------------------------------------
