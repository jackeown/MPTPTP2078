%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t76_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:32 EDT 2019

% Result     : Theorem 63.64s
% Output     : Refutation 63.64s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 243 expanded)
%              Number of leaves         :   33 (  88 expanded)
%              Depth                    :    8
%              Number of atoms          :  357 ( 742 expanded)
%              Number of equality atoms :   71 ( 163 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31550,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f214,f215,f222,f743,f745,f968,f15239,f16678,f16782,f16912,f17370,f17806,f18477,f18760,f21086,f21641,f31470,f31527,f31547])).

fof(f31547,plain,
    ( ~ spl5_41
    | ~ spl5_75
    | spl5_2
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f31503,f809,f209,f949,f741])).

fof(f741,plain,
    ( spl5_41
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f949,plain,
    ( spl5_75
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f209,plain,
    ( spl5_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f809,plain,
    ( spl5_52
  <=> k1_tops_1(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f31503,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_52 ),
    inference(superposition,[],[f141,f810])).

fof(f810,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f809])).

fof(f141,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',l78_tops_1)).

fof(f31527,plain,
    ( spl5_1
    | ~ spl5_52 ),
    inference(avatar_contradiction_clause,[],[f31471])).

fof(f31471,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f127,f128,f207,f126,f810,f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X1,X0) != X0
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(X0,X1) ) ),
    inference(condensation,[],[f200])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) != X1
      | v3_pre_topc(X1,X0) ) ),
    inference(condensation,[],[f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k1_tops_1(X0,X2) != X2
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
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
    inference(flattening,[],[f80])).

fof(f80,plain,(
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
    inference(ennf_transformation,[],[f59])).

fof(f59,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',t55_tops_1)).

fof(f126,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',t76_tops_1)).

fof(f207,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl5_1
  <=> ~ v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f128,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f127,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f31470,plain,
    ( ~ spl5_597
    | spl5_646
    | ~ spl5_816 ),
    inference(avatar_split_clause,[],[f31463,f21639,f17604,f17361])).

fof(f17361,plain,
    ( spl5_597
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_597])])).

fof(f17604,plain,
    ( spl5_646
  <=> k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_646])])).

fof(f21639,plain,
    ( spl5_816
  <=> k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_816])])).

fof(f31463,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl5_816 ),
    inference(superposition,[],[f195,f21640])).

fof(f21640,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = sK1
    | ~ spl5_816 ),
    inference(avatar_component_clause,[],[f21639])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f179,f149])).

fof(f149,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',redefinition_k6_subset_1)).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',redefinition_k7_subset_1)).

fof(f21641,plain,
    ( ~ spl5_621
    | spl5_816
    | ~ spl5_597
    | ~ spl5_760 ),
    inference(avatar_split_clause,[],[f21634,f21084,f17361,f21639,f17445])).

fof(f17445,plain,
    ( spl5_621
  <=> ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_621])])).

fof(f21084,plain,
    ( spl5_760
  <=> k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_760])])).

fof(f21634,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = sK1
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl5_760 ),
    inference(forward_demodulation,[],[f21617,f21085])).

fof(f21085,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1
    | ~ spl5_760 ),
    inference(avatar_component_clause,[],[f21084])).

fof(f21617,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = sK1
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl5_760 ),
    inference(superposition,[],[f2069,f21085])).

fof(f2069,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X1,k3_subset_1(X1,X0),X0) = k3_subset_1(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ) ),
    inference(condensation,[],[f2062])).

fof(f2062,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,k3_subset_1(X0,X1),X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f176,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',t32_subset_1)).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',idempotence_k9_subset_1)).

fof(f21086,plain,
    ( ~ spl5_597
    | spl5_760
    | ~ spl5_598 ),
    inference(avatar_split_clause,[],[f21062,f17367,f21084,f17361])).

fof(f17367,plain,
    ( spl5_598
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_598])])).

fof(f21062,plain,
    ( k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl5_598 ),
    inference(superposition,[],[f157,f17368])).

fof(f17368,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_598 ),
    inference(avatar_component_clause,[],[f17367])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',involutiveness_k3_subset_1)).

fof(f18760,plain,
    ( ~ spl5_556
    | spl5_621 ),
    inference(avatar_contradiction_clause,[],[f18754])).

fof(f18754,plain,
    ( $false
    | ~ spl5_556
    | ~ spl5_621 ),
    inference(subsumption_resolution,[],[f17296,f17446])).

fof(f17446,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl5_621 ),
    inference(avatar_component_clause,[],[f17445])).

fof(f17296,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl5_556 ),
    inference(superposition,[],[f148,f16772])).

fof(f16772,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_556 ),
    inference(avatar_component_clause,[],[f16771])).

fof(f16771,plain,
    ( spl5_556
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_556])])).

fof(f148,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',dt_k6_subset_1)).

fof(f18477,plain,
    ( ~ spl5_41
    | ~ spl5_75
    | spl5_52
    | ~ spl5_646 ),
    inference(avatar_split_clause,[],[f18428,f17604,f809,f949,f741])).

fof(f18428,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_646 ),
    inference(superposition,[],[f1873,f17605])).

fof(f17605,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = sK1
    | ~ spl5_646 ),
    inference(avatar_component_clause,[],[f17604])).

fof(f1873,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f1870])).

fof(f1870,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f195,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',t74_tops_1)).

fof(f17806,plain,
    ( ~ spl5_38
    | spl5_597 ),
    inference(avatar_contradiction_clause,[],[f17802])).

fof(f17802,plain,
    ( $false
    | ~ spl5_38
    | ~ spl5_597 ),
    inference(unit_resulting_resolution,[],[f736,f17362,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',t3_subset)).

fof(f17362,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl5_597 ),
    inference(avatar_component_clause,[],[f17361])).

fof(f736,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f735])).

fof(f735,plain,
    ( spl5_38
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f17370,plain,
    ( ~ spl5_597
    | spl5_598
    | ~ spl5_556 ),
    inference(avatar_split_clause,[],[f17298,f16771,f17367,f17361])).

fof(f17298,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl5_556 ),
    inference(superposition,[],[f194,f16772])).

fof(f194,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f158,f149])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',d5_subset_1)).

fof(f16912,plain,(
    spl5_35 ),
    inference(avatar_contradiction_clause,[],[f16907])).

fof(f16907,plain,
    ( $false
    | ~ spl5_35 ),
    inference(unit_resulting_resolution,[],[f128,f126,f649,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',dt_k2_pre_topc)).

fof(f649,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f648])).

fof(f648,plain,
    ( spl5_35
  <=> ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f16782,plain,
    ( ~ spl5_35
    | spl5_556
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f16761,f209,f16771,f648])).

fof(f16761,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(superposition,[],[f195,f210])).

fof(f210,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f209])).

fof(f16678,plain,
    ( ~ spl5_41
    | ~ spl5_1
    | spl5_52
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f15444,f217,f809,f206,f741])).

fof(f217,plain,
    ( spl5_4
  <=> ! [X1,X3] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f15444,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f218,f126])).

fof(f218,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f217])).

fof(f15239,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f15193])).

fof(f15193,plain,
    ( $false
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f128,f127,f144,f221])).

fof(f221,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl5_6
  <=> ! [X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f144,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',existence_m1_subset_1)).

fof(f968,plain,(
    spl5_75 ),
    inference(avatar_contradiction_clause,[],[f958])).

fof(f958,plain,
    ( $false
    | ~ spl5_75 ),
    inference(subsumption_resolution,[],[f126,f950])).

fof(f950,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f949])).

fof(f745,plain,(
    spl5_41 ),
    inference(avatar_contradiction_clause,[],[f744])).

fof(f744,plain,
    ( $false
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f128,f742])).

fof(f742,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f741])).

fof(f743,plain,
    ( spl5_38
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f727,f741,f735])).

fof(f727,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f137,f126])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t76_tops_1.p',t48_pre_topc)).

fof(f222,plain,
    ( spl5_4
    | spl5_6 ),
    inference(avatar_split_clause,[],[f143,f220,f217])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f215,plain,
    ( spl5_0
    | spl5_2 ),
    inference(avatar_split_clause,[],[f124,f209,f203])).

fof(f203,plain,
    ( spl5_0
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f124,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f214,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f125,f212,f206])).

fof(f212,plain,
    ( spl5_3
  <=> k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f125,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
