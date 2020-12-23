%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t21_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:37 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 163 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  230 ( 494 expanded)
%              Number of equality atoms :    9 (  33 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f835,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f91,f95,f99,f129,f134,f834])).

fof(f834,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f833])).

fof(f833,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f133,f830])).

fof(f830,plain,
    ( ! [X0] : v1_tops_2(k3_xboole_0(sK1,X0),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(superposition,[],[f826,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t21_tops_2.p',commutativity_k3_xboole_0)).

fof(f826,plain,
    ( ! [X1] : v1_tops_2(k3_xboole_0(X1,sK1),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f821,f480])).

fof(f480,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK0,k3_xboole_0(X1,sK1)),sK1)
        | v1_tops_2(k3_xboole_0(X1,sK1),sK0) )
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f470,f252])).

fof(f252,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(sK3(sK0,k3_xboole_0(X4,sK1)),sK0)
        | v1_tops_2(k3_xboole_0(X4,sK1),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f251,f120])).

fof(f120,plain,
    ( ! [X3] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X3,sK1) = k3_xboole_0(X3,sK1)
    | ~ spl8_6 ),
    inference(resolution,[],[f98,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t21_tops_2.p',redefinition_k9_subset_1)).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl8_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f251,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(sK3(sK0,k3_xboole_0(X4,sK1)),sK0)
        | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X4,sK1),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f250,f120])).

fof(f250,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(sK3(sK0,k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X4,sK1)),sK0)
        | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X4,sK1),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f231,f86])).

fof(f86,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl8_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f231,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(sK0)
        | ~ v3_pre_topc(sK3(sK0,k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X4,sK1)),sK0)
        | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X4,sK1),sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f119,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t21_tops_2.p',d1_tops_2)).

fof(f119,plain,
    ( ! [X2] : m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X2,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_6 ),
    inference(resolution,[],[f98,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t21_tops_2.p',dt_k9_subset_1)).

fof(f470,plain,
    ( ! [X1] :
        ( v1_tops_2(k3_xboole_0(X1,sK1),sK0)
        | ~ r2_hidden(sK3(sK0,k3_xboole_0(X1,sK1)),sK1)
        | v3_pre_topc(sK3(sK0,k3_xboole_0(X1,sK1)),sK0) )
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(resolution,[],[f246,f124])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0) )
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f123,f90])).

fof(f90,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_2
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0)
        | ~ v1_tops_2(sK1,sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f114,f86])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0)
        | ~ v1_tops_2(sK1,sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f98,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v3_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f246,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(sK0,k3_xboole_0(X2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_2(k3_xboole_0(X2,sK1),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f245,f120])).

fof(f245,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(sK0,k3_xboole_0(X2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X2,sK1),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f244,f120])).

fof(f244,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(sK0,k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X2,sK1),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f229,f86])).

fof(f229,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | m1_subset_1(sK3(sK0,k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X2,sK1),sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f119,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f821,plain,
    ( ! [X1] :
        ( v1_tops_2(k3_xboole_0(X1,sK1),sK0)
        | r2_hidden(sK3(sK0,k3_xboole_0(X1,sK1)),sK1) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(resolution,[],[f498,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t21_tops_2.p',d4_xboole_0)).

fof(f498,plain,
    ( ! [X0] :
        ( sP7(sK3(sK0,k3_xboole_0(X0,sK1)),sK1,X0)
        | v1_tops_2(k3_xboole_0(X0,sK1),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(resolution,[],[f249,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f249,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(sK0,k3_xboole_0(X3,sK1)),k3_xboole_0(X3,sK1))
        | v1_tops_2(k3_xboole_0(X3,sK1),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f248,f120])).

fof(f248,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(sK0,k3_xboole_0(X3,sK1)),k3_xboole_0(X3,sK1))
        | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X3,sK1),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f247,f120])).

fof(f247,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(sK0,k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X3,sK1)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X3,sK1))
        | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X3,sK1),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f230,f86])).

fof(f230,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | r2_hidden(sK3(sK0,k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X3,sK1)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X3,sK1))
        | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X3,sK1),sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f119,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f133,plain,
    ( ~ v1_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_11
  <=> ~ v1_tops_2(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f134,plain,
    ( ~ spl8_11
    | ~ spl8_4
    | spl8_9 ),
    inference(avatar_split_clause,[],[f130,f127,f93,f132])).

fof(f93,plain,
    ( spl8_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f127,plain,
    ( spl8_9
  <=> ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f130,plain,
    ( ~ v1_tops_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f128,f106])).

fof(f106,plain,
    ( ! [X3] : k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X3,sK2) = k3_xboole_0(X3,sK2)
    | ~ spl8_4 ),
    inference(resolution,[],[f94,f57])).

fof(f94,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f128,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f53,f127])).

fof(f53,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t21_tops_2.p',t21_tops_2)).

fof(f99,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f54,f97])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f51,f93])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f52,f89])).

fof(f52,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f55,f85])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
