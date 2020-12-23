%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1708+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:29 EST 2020

% Result     : Theorem 8.86s
% Output     : Refutation 8.86s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 385 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  626 (3058 expanded)
%              Number of equality atoms :   25 ( 375 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5073,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4650,f4733,f4743,f4753,f4779,f4787,f4980,f5002,f5059,f5072])).

fof(f5072,plain,
    ( spl115_1
    | ~ spl115_11
    | spl115_12 ),
    inference(avatar_contradiction_clause,[],[f5071])).

fof(f5071,plain,
    ( $false
    | spl115_1
    | ~ spl115_11
    | spl115_12 ),
    inference(subsumption_resolution,[],[f4693,f4968])).

fof(f4968,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl115_11
    | spl115_12 ),
    inference(resolution,[],[f4921,f4583])).

fof(f4583,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f3856])).

fof(f3856,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f4921,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl115_11
    | spl115_12 ),
    inference(subsumption_resolution,[],[f4808,f4765])).

fof(f4765,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl115_12 ),
    inference(avatar_component_clause,[],[f4763])).

fof(f4763,plain,
    ( spl115_12
  <=> v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl115_12])])).

fof(f4808,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl115_11 ),
    inference(resolution,[],[f4732,f4086])).

fof(f4086,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3572])).

fof(f3572,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f3571])).

fof(f3571,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f4732,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl115_11 ),
    inference(avatar_component_clause,[],[f4730])).

fof(f4730,plain,
    ( spl115_11
  <=> m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl115_11])])).

fof(f4693,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl115_1 ),
    inference(subsumption_resolution,[],[f4680,f4083])).

fof(f4083,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f3567])).

fof(f3567,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f4680,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | spl115_1 ),
    inference(resolution,[],[f4645,f4093])).

fof(f4093,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3577])).

fof(f3577,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f4645,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl115_1 ),
    inference(avatar_component_clause,[],[f4643])).

fof(f4643,plain,
    ( spl115_1
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl115_1])])).

fof(f5059,plain,
    ( spl115_10
    | ~ spl115_13
    | ~ spl115_18 ),
    inference(avatar_contradiction_clause,[],[f5058])).

fof(f5058,plain,
    ( $false
    | spl115_10
    | ~ spl115_13
    | ~ spl115_18 ),
    inference(subsumption_resolution,[],[f5057,f4727])).

fof(f4727,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl115_10 ),
    inference(avatar_component_clause,[],[f4726])).

fof(f4726,plain,
    ( spl115_10
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl115_10])])).

fof(f5057,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl115_13
    | ~ spl115_18 ),
    inference(subsumption_resolution,[],[f5055,f4769])).

fof(f4769,plain,
    ( l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl115_13 ),
    inference(avatar_component_clause,[],[f4768])).

fof(f4768,plain,
    ( spl115_13
  <=> l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl115_13])])).

fof(f5055,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl115_18 ),
    inference(resolution,[],[f4929,f3896])).

fof(f3896,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3445])).

fof(f3445,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3444])).

fof(f3444,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f4929,plain,
    ( v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl115_18 ),
    inference(avatar_component_clause,[],[f4927])).

fof(f4927,plain,
    ( spl115_18
  <=> v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl115_18])])).

fof(f5002,plain,
    ( ~ spl115_8
    | ~ spl115_9
    | spl115_10
    | ~ spl115_12
    | spl115_18 ),
    inference(avatar_contradiction_clause,[],[f5001])).

fof(f5001,plain,
    ( $false
    | ~ spl115_8
    | ~ spl115_9
    | spl115_10
    | ~ spl115_12
    | spl115_18 ),
    inference(subsumption_resolution,[],[f4764,f5000])).

fof(f5000,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl115_8
    | ~ spl115_9
    | spl115_10
    | spl115_18 ),
    inference(subsumption_resolution,[],[f4999,f3779])).

fof(f3779,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3366])).

fof(f3366,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3365])).

fof(f3365,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3354])).

fof(f3354,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f3347])).

fof(f3347,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3346])).

fof(f3346,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f4999,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK0)
    | ~ spl115_8
    | ~ spl115_9
    | spl115_10
    | spl115_18 ),
    inference(subsumption_resolution,[],[f4998,f4719])).

fof(f4719,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl115_8 ),
    inference(avatar_component_clause,[],[f4718])).

fof(f4718,plain,
    ( spl115_8
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl115_8])])).

fof(f4998,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl115_9
    | spl115_10
    | spl115_18 ),
    inference(subsumption_resolution,[],[f4997,f4723])).

fof(f4723,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl115_9 ),
    inference(avatar_component_clause,[],[f4722])).

fof(f4722,plain,
    ( spl115_9
  <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl115_9])])).

fof(f4997,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl115_10
    | spl115_18 ),
    inference(subsumption_resolution,[],[f4996,f4727])).

fof(f4996,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl115_18 ),
    inference(subsumption_resolution,[],[f4995,f3776])).

fof(f3776,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f3366])).

fof(f4995,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl115_18 ),
    inference(subsumption_resolution,[],[f4994,f3775])).

fof(f3775,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3366])).

fof(f4994,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl115_18 ),
    inference(subsumption_resolution,[],[f4993,f3774])).

fof(f3774,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3366])).

fof(f4993,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl115_18 ),
    inference(subsumption_resolution,[],[f4992,f3778])).

fof(f3778,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3366])).

fof(f4992,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl115_18 ),
    inference(subsumption_resolution,[],[f4991,f3777])).

fof(f3777,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3366])).

fof(f4991,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl115_18 ),
    inference(subsumption_resolution,[],[f4957,f3781])).

fof(f3781,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3366])).

fof(f4957,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl115_18 ),
    inference(superposition,[],[f4928,f4573])).

fof(f4573,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f3787])).

fof(f3787,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f3370])).

fof(f3370,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3369])).

fof(f3369,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3327])).

fof(f3327,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f4928,plain,
    ( ~ v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | spl115_18 ),
    inference(avatar_component_clause,[],[f4927])).

fof(f4764,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl115_12 ),
    inference(avatar_component_clause,[],[f4763])).

fof(f4980,plain,
    ( spl115_2
    | ~ spl115_11
    | spl115_12 ),
    inference(avatar_contradiction_clause,[],[f4979])).

fof(f4979,plain,
    ( $false
    | spl115_2
    | ~ spl115_11
    | spl115_12 ),
    inference(subsumption_resolution,[],[f4967,f4700])).

fof(f4700,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | spl115_2 ),
    inference(subsumption_resolution,[],[f4696,f4083])).

fof(f4696,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | spl115_2 ),
    inference(resolution,[],[f4649,f4093])).

fof(f4649,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl115_2 ),
    inference(avatar_component_clause,[],[f4647])).

fof(f4647,plain,
    ( spl115_2
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl115_2])])).

fof(f4967,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl115_11
    | spl115_12 ),
    inference(resolution,[],[f4921,f4584])).

fof(f4584,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f3855])).

fof(f3855,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4787,plain,
    ( ~ spl115_8
    | spl115_13 ),
    inference(avatar_contradiction_clause,[],[f4786])).

fof(f4786,plain,
    ( $false
    | ~ spl115_8
    | spl115_13 ),
    inference(subsumption_resolution,[],[f4785,f4782])).

fof(f4782,plain,
    ( l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl115_8 ),
    inference(subsumption_resolution,[],[f4780,f3781])).

fof(f4780,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl115_8 ),
    inference(resolution,[],[f4719,f3816])).

fof(f3816,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3395])).

fof(f3395,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f4785,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl115_13 ),
    inference(resolution,[],[f4770,f3899])).

fof(f3899,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3449])).

fof(f3449,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f4770,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl115_13 ),
    inference(avatar_component_clause,[],[f4768])).

fof(f4779,plain,(
    ~ spl115_10 ),
    inference(avatar_contradiction_clause,[],[f4778])).

fof(f4778,plain,
    ( $false
    | ~ spl115_10 ),
    inference(subsumption_resolution,[],[f4777,f3779])).

fof(f4777,plain,
    ( v2_struct_0(sK0)
    | ~ spl115_10 ),
    inference(subsumption_resolution,[],[f4776,f3775])).

fof(f4776,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl115_10 ),
    inference(subsumption_resolution,[],[f4775,f3774])).

fof(f4775,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl115_10 ),
    inference(subsumption_resolution,[],[f4774,f3778])).

fof(f4774,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl115_10 ),
    inference(subsumption_resolution,[],[f4773,f3777])).

fof(f4773,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl115_10 ),
    inference(subsumption_resolution,[],[f4772,f3781])).

fof(f4772,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl115_10 ),
    inference(resolution,[],[f4728,f3783])).

fof(f3783,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3368])).

fof(f3368,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3367])).

fof(f3367,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3330])).

fof(f3330,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f4728,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl115_10 ),
    inference(avatar_component_clause,[],[f4726])).

fof(f4753,plain,(
    spl115_8 ),
    inference(avatar_contradiction_clause,[],[f4752])).

fof(f4752,plain,
    ( $false
    | spl115_8 ),
    inference(subsumption_resolution,[],[f4751,f3779])).

fof(f4751,plain,
    ( v2_struct_0(sK0)
    | spl115_8 ),
    inference(subsumption_resolution,[],[f4750,f3775])).

fof(f4750,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl115_8 ),
    inference(subsumption_resolution,[],[f4749,f3774])).

fof(f4749,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl115_8 ),
    inference(subsumption_resolution,[],[f4748,f3778])).

fof(f4748,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl115_8 ),
    inference(subsumption_resolution,[],[f4747,f3777])).

fof(f4747,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl115_8 ),
    inference(subsumption_resolution,[],[f4746,f3781])).

fof(f4746,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl115_8 ),
    inference(resolution,[],[f4720,f3785])).

fof(f3785,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3368])).

fof(f4720,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl115_8 ),
    inference(avatar_component_clause,[],[f4718])).

fof(f4743,plain,(
    spl115_9 ),
    inference(avatar_contradiction_clause,[],[f4742])).

fof(f4742,plain,
    ( $false
    | spl115_9 ),
    inference(subsumption_resolution,[],[f4741,f3779])).

fof(f4741,plain,
    ( v2_struct_0(sK0)
    | spl115_9 ),
    inference(subsumption_resolution,[],[f4740,f3775])).

fof(f4740,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl115_9 ),
    inference(subsumption_resolution,[],[f4739,f3774])).

fof(f4739,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl115_9 ),
    inference(subsumption_resolution,[],[f4738,f3778])).

fof(f4738,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl115_9 ),
    inference(subsumption_resolution,[],[f4737,f3777])).

fof(f4737,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl115_9 ),
    inference(subsumption_resolution,[],[f4736,f3781])).

fof(f4736,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl115_9 ),
    inference(resolution,[],[f4724,f3784])).

fof(f3784,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3368])).

fof(f4724,plain,
    ( ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl115_9 ),
    inference(avatar_component_clause,[],[f4722])).

fof(f4733,plain,
    ( ~ spl115_8
    | ~ spl115_9
    | spl115_10
    | spl115_11 ),
    inference(avatar_split_clause,[],[f4716,f4730,f4726,f4722,f4718])).

fof(f4716,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f4715,f3779])).

fof(f4715,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4714,f3776])).

fof(f4714,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4713,f3775])).

fof(f4713,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4712,f3774])).

fof(f4712,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4711,f3778])).

fof(f4711,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4710,f3777])).

fof(f4710,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4707,f3781])).

fof(f4707,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f3773,f4573])).

fof(f3773,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f3366])).

fof(f4650,plain,
    ( ~ spl115_1
    | ~ spl115_2 ),
    inference(avatar_split_clause,[],[f4572,f4647,f4643])).

fof(f4572,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f4571])).

fof(f4571,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(equality_resolution,[],[f3772])).

fof(f3772,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f3366])).
%------------------------------------------------------------------------------
