%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t22_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:37 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 153 expanded)
%              Number of leaves         :   10 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  216 ( 464 expanded)
%              Number of equality atoms :    6 (  31 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f597,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f85,f93,f117,f122,f596])).

fof(f596,plain,
    ( ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f121,f592])).

fof(f592,plain,
    ( ! [X0] : v1_tops_2(k4_xboole_0(sK1,X0),sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f588,f499])).

fof(f499,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK1,X1)),sK1)
        | v1_tops_2(k4_xboole_0(sK1,X1),sK0) )
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f493,f226])).

fof(f226,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(sK3(sK0,k4_xboole_0(sK1,X4)),sK0)
        | v1_tops_2(k4_xboole_0(sK1,X4),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f225,f110])).

fof(f110,plain,
    ( ! [X2] : k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2) = k4_xboole_0(sK1,X2)
    | ~ spl8_6 ),
    inference(resolution,[],[f92,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t22_tops_2.p',redefinition_k7_subset_1)).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f225,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(sK3(sK0,k4_xboole_0(sK1,X4)),sK0)
        | v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X4),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f224,f110])).

fof(f224,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(sK3(sK0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X4)),sK0)
        | v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X4),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f210,f80])).

fof(f80,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f210,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(sK0)
        | ~ v3_pre_topc(sK3(sK0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X4)),sK0)
        | v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X4),sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f109,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t22_tops_2.p',d1_tops_2)).

fof(f109,plain,
    ( ! [X1] : m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl8_6 ),
    inference(resolution,[],[f92,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t22_tops_2.p',dt_k7_subset_1)).

fof(f493,plain,
    ( ! [X1] :
        ( v1_tops_2(k4_xboole_0(sK1,X1),sK0)
        | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK1,X1)),sK1)
        | v3_pre_topc(sK3(sK0,k4_xboole_0(sK1,X1)),sK0) )
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(resolution,[],[f220,f113])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0) )
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f112,f84])).

fof(f84,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_2
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0)
        | ~ v1_tops_2(sK1,sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f105,f80])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0)
        | ~ v1_tops_2(sK1,sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f92,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v3_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f220,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(sK0,k4_xboole_0(sK1,X2)),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_2(k4_xboole_0(sK1,X2),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f219,f110])).

fof(f219,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(sK0,k4_xboole_0(sK1,X2)),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f218,f110])).

fof(f218,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(sK0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f208,f80])).

fof(f208,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | m1_subset_1(sK3(sK0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f109,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f588,plain,
    ( ! [X0] :
        ( v1_tops_2(k4_xboole_0(sK1,X0),sK0)
        | r2_hidden(sK3(sK0,k4_xboole_0(sK1,X0)),sK1) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(resolution,[],[f502,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t22_tops_2.p',d5_xboole_0)).

fof(f502,plain,
    ( ! [X0] :
        ( sP7(sK3(sK0,k4_xboole_0(sK1,X0)),X0,sK1)
        | v1_tops_2(k4_xboole_0(sK1,X0),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(resolution,[],[f223,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f223,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,X3)),k4_xboole_0(sK1,X3))
        | v1_tops_2(k4_xboole_0(sK1,X3),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f222,f110])).

fof(f222,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,X3)),k4_xboole_0(sK1,X3))
        | v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X3),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f221,f110])).

fof(f221,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(sK0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X3)),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X3))
        | v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X3),sK0) )
    | ~ spl8_0
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f209,f80])).

fof(f209,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | r2_hidden(sK3(sK0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X3)),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X3))
        | v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X3),sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f109,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f121,plain,
    ( ~ v1_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_11
  <=> ~ v1_tops_2(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f122,plain,
    ( ~ spl8_11
    | ~ spl8_6
    | spl8_9 ),
    inference(avatar_split_clause,[],[f118,f115,f91,f120])).

fof(f115,plain,
    ( spl8_9
  <=> ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f118,plain,
    ( ~ v1_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f116,f110])).

fof(f116,plain,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f48,f115])).

fof(f48,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
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
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t22_tops_2.p',t22_tops_2)).

fof(f93,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f49,f91])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f47,f83])).

fof(f47,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f50,f79])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
