%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t1_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:07 EDT 2019

% Result     : Theorem 14.93s
% Output     : Refutation 14.93s
% Verified   : 
% Statistics : Number of formulae       :  271 (1483 expanded)
%              Number of leaves         :   33 ( 356 expanded)
%              Depth                    :   15
%              Number of atoms          : 1142 (11830 expanded)
%              Number of equality atoms :   11 ( 201 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9056,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f693,f803,f815,f821,f832,f843,f867,f872,f882,f1751,f5224,f5433,f5462,f5468,f5555,f5571,f5672,f5923,f5998,f8018,f8133,f8165,f8917,f9049])).

fof(f9049,plain,
    ( ~ spl8_28
    | ~ spl8_38
    | spl8_153 ),
    inference(avatar_contradiction_clause,[],[f9048])).

fof(f9048,plain,
    ( $false
    | ~ spl8_28
    | ~ spl8_38
    | ~ spl8_153 ),
    inference(subsumption_resolution,[],[f8933,f8132])).

fof(f8132,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl8_153 ),
    inference(avatar_component_clause,[],[f8131])).

fof(f8131,plain,
    ( spl8_153
  <=> ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_153])])).

fof(f8933,plain,
    ( r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl8_28
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f96,f95,f94,f1747,f92,f91,f93,f8607,f200])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | r2_hidden(k4_lattices(X0,X1,X2),sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X2,sK1)
      | ~ v19_lattices(sK1,X0)
      | ~ v20_lattices(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f199,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t1_filter_1.p',t4_subset)).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_lattices(X0,X1,X2),sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X2,sK1)
      | ~ v19_lattices(sK1,X0)
      | ~ v20_lattices(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f183,f130])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_lattices(X0,X1,X2),sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X2,sK1)
      | ~ v19_lattices(sK1,X0)
      | ~ v20_lattices(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f90,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(k4_lattices(X0,X2,X3),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X3,X1)
      | v1_xboole_0(X1)
      | ~ v19_lattices(X1,X0)
      | ~ v20_lattices(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ! [X3] :
                    ( ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                    <=> r2_hidden(k4_lattices(X0,X2,X3),X1) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ! [X3] :
                    ( ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                    <=> r2_hidden(k4_lattices(X0,X2,X3),X1) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                    <=> r2_hidden(k4_lattices(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t1_filter_1.p',t8_filter_0)).

fof(f90,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v20_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v19_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                | v1_xboole_0(k9_subset_1(u1_struct_0(X0),X1,X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X2,X0)
              & v19_lattices(X2,X0)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v20_lattices(X1,X0)
          & v19_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v20_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v19_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                | v1_xboole_0(k9_subset_1(u1_struct_0(X0),X1,X2)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X2,X0)
              & v19_lattices(X2,X0)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v20_lattices(X1,X0)
          & v19_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v20_lattices(X2,X0)
                  & v19_lattices(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v20_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                  & v19_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                  & ~ v1_xboole_0(k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v20_lattices(X2,X0)
                & v19_lattices(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ( m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v20_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v19_lattices(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ~ v1_xboole_0(k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t1_filter_1.p',t1_filter_1)).

fof(f8607,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ spl8_28 ),
    inference(resolution,[],[f742,f135])).

fof(f135,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
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
    file('/export/starexec/sandbox2/benchmark/filter_1__t1_filter_1.p',d4_xboole_0)).

fof(f742,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f741])).

fof(f741,plain,
    ( spl8_28
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f93,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f91,plain,(
    v19_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f92,plain,(
    v20_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f1747,plain,
    ( r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f1746])).

fof(f1746,plain,
    ( spl8_38
  <=> r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f94,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f95,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f96,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f8917,plain,
    ( ~ spl8_26
    | ~ spl8_40
    | spl8_151 ),
    inference(avatar_contradiction_clause,[],[f8916])).

fof(f8916,plain,
    ( $false
    | ~ spl8_26
    | ~ spl8_40
    | ~ spl8_151 ),
    inference(subsumption_resolution,[],[f8805,f8126])).

fof(f8126,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl8_151 ),
    inference(avatar_component_clause,[],[f8125])).

fof(f8125,plain,
    ( spl8_151
  <=> ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_151])])).

fof(f8805,plain,
    ( r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl8_26
    | ~ spl8_40 ),
    inference(unit_resulting_resolution,[],[f96,f1780,f94,f95,f88,f87,f89,f5513,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | r2_hidden(k4_lattices(X0,X1,X2),sK2)
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X2,sK2)
      | ~ v19_lattices(sK2,X0)
      | ~ v20_lattices(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f178,f130])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_lattices(X0,X1,X2),sK2)
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X2,sK2)
      | ~ v19_lattices(sK2,X0)
      | ~ v20_lattices(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f162,f130])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_lattices(X0,X1,X2),sK2)
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X2,sK2)
      | ~ v19_lattices(sK2,X0)
      | ~ v20_lattices(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f86,f102])).

fof(f86,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f5513,plain,
    ( r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f727,f134])).

fof(f134,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f727,plain,
    ( r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f726])).

fof(f726,plain,
    ( spl8_26
  <=> r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f87,plain,(
    v19_lattices(sK2,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f88,plain,(
    v20_lattices(sK2,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f1780,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f1779,plain,
    ( spl8_40
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f8165,plain,
    ( ~ spl8_28
    | spl8_41 ),
    inference(avatar_contradiction_clause,[],[f8164])).

fof(f8164,plain,
    ( $false
    | ~ spl8_28
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f742,f7405])).

fof(f7405,plain,
    ( ! [X1] : ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(X1,sK2))
    | ~ spl8_41 ),
    inference(resolution,[],[f1783,f134])).

fof(f1783,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f1782])).

fof(f1782,plain,
    ( spl8_41
  <=> ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f8133,plain,
    ( ~ spl8_151
    | ~ spl8_153
    | spl8_25 ),
    inference(avatar_split_clause,[],[f6939,f717,f8131,f8125])).

fof(f717,plain,
    ( spl8_25
  <=> ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f6939,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl8_25 ),
    inference(resolution,[],[f718,f133])).

fof(f133,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f718,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f717])).

fof(f8018,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f8017])).

fof(f8017,plain,
    ( $false
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f7997,f1050])).

fof(f1050,plain,(
    r2_hidden(k3_lattices(sK0,sK3(sK2),sK3(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f95,f94,f96,f90,f92,f91,f422,f182,f93,f479,f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v1_xboole_0(X3)
      | ~ v19_lattices(X3,X0)
      | ~ v20_lattices(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k3_lattices(X0,X2,X1),X3) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(k3_lattices(X0,X2,X1),X3)
                    & r2_hidden(k3_lattices(X0,X1,X2),X3) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v20_lattices(X3,X0)
                  | ~ v19_lattices(X3,X0)
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(k3_lattices(X0,X2,X1),X3)
                    & r2_hidden(k3_lattices(X0,X1,X2),X3) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v20_lattices(X3,X0)
                  | ~ v19_lattices(X3,X0)
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v20_lattices(X3,X0)
                    & v19_lattices(X3,X0)
                    & ~ v1_xboole_0(X3) )
                 => ( r2_hidden(X1,X3)
                   => ( r2_hidden(k3_lattices(X0,X2,X1),X3)
                      & r2_hidden(k3_lattices(X0,X1,X2),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t1_filter_1.p',t10_filter_0)).

fof(f479,plain,(
    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f93,f182,f130])).

fof(f182,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f101,f90,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t1_filter_1.p',t2_subset)).

fof(f101,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t1_filter_1.p',existence_m1_subset_1)).

fof(f422,plain,(
    m1_subset_1(sK3(sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f89,f161,f130])).

fof(f161,plain,(
    r2_hidden(sK3(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f101,f86,f120])).

fof(f7997,plain,
    ( ~ r2_hidden(k3_lattices(sK0,sK3(sK2),sK3(sK1)),sK1)
    | ~ spl8_6 ),
    inference(resolution,[],[f1043,f6330])).

fof(f6330,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_6 ),
    inference(resolution,[],[f6151,f133])).

fof(f6151,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f6005,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t1_filter_1.p',t7_boole)).

fof(f6005,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f159,f371])).

fof(f371,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f89,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t1_filter_1.p',redefinition_k9_subset_1)).

fof(f159,plain,
    ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl8_6
  <=> v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f1043,plain,(
    r2_hidden(k3_lattices(sK0,sK3(sK2),sK3(sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f95,f94,f96,f86,f88,f87,f161,f422,f89,f479,f115])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v1_xboole_0(X3)
      | ~ v19_lattices(X3,X0)
      | ~ v20_lattices(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k3_lattices(X0,X1,X2),X3) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f5998,plain,
    ( ~ spl8_41
    | ~ spl8_43
    | spl8_29 ),
    inference(avatar_split_clause,[],[f5592,f738,f1788,f1782])).

fof(f1788,plain,
    ( spl8_43
  <=> ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f738,plain,
    ( spl8_29
  <=> ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f5592,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ spl8_29 ),
    inference(resolution,[],[f739,f133])).

fof(f739,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f738])).

fof(f5923,plain,
    ( ~ spl8_24
    | ~ spl8_32
    | ~ spl8_34
    | spl8_43 ),
    inference(avatar_contradiction_clause,[],[f5922])).

fof(f5922,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_43 ),
    inference(subsumption_resolution,[],[f5867,f3063])).

fof(f3063,plain,
    ( r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl8_24 ),
    inference(resolution,[],[f721,f135])).

fof(f721,plain,
    ( r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f720])).

fof(f720,plain,
    ( spl8_24
  <=> r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f5867,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_43 ),
    inference(unit_resulting_resolution,[],[f96,f95,f94,f92,f91,f831,f93,f842,f1789,f184])).

fof(f184,plain,(
    ! [X4,X5,X3] :
      ( ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r2_hidden(k4_lattices(X3,X4,X5),sK1)
      | r2_hidden(X4,sK1)
      | ~ v19_lattices(sK1,X3)
      | ~ v20_lattices(sK1,X3)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(resolution,[],[f90,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(k4_lattices(X0,X2,X3),X1)
      | r2_hidden(X2,X1)
      | v1_xboole_0(X1)
      | ~ v19_lattices(X1,X0)
      | ~ v20_lattices(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1789,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f1788])).

fof(f842,plain,
    ( m1_subset_1(sK4(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f841])).

fof(f841,plain,
    ( spl8_34
  <=> m1_subset_1(sK4(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f831,plain,
    ( m1_subset_1(sK5(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f830])).

fof(f830,plain,
    ( spl8_32
  <=> m1_subset_1(sK5(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f5672,plain,
    ( ~ spl8_24
    | ~ spl8_32
    | ~ spl8_34
    | spl8_41 ),
    inference(avatar_contradiction_clause,[],[f5671])).

fof(f5671,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f5616,f3064])).

fof(f3064,plain,
    ( r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl8_24 ),
    inference(resolution,[],[f721,f134])).

fof(f5616,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_41 ),
    inference(unit_resulting_resolution,[],[f96,f95,f94,f88,f87,f831,f89,f842,f1783,f163])).

fof(f163,plain,(
    ! [X4,X5,X3] :
      ( ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r2_hidden(k4_lattices(X3,X4,X5),sK2)
      | r2_hidden(X4,sK2)
      | ~ v19_lattices(sK2,X3)
      | ~ v20_lattices(sK2,X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(resolution,[],[f86,f103])).

fof(f5571,plain,
    ( ~ spl8_29
    | ~ spl8_25
    | spl8_5
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f5570,f726,f152,f717,f738])).

fof(f152,plain,
    ( spl8_5
  <=> ~ v19_lattices(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f5570,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f5569,f883])).

fof(f883,plain,
    ( ~ v19_lattices(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f153,f371])).

fof(f153,plain,
    ( ~ v19_lattices(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f5569,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | v19_lattices(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f5530,f1401])).

fof(f1401,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f474,f128])).

fof(f128,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t1_filter_1.p',commutativity_k3_xboole_0)).

fof(f474,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f449,f450])).

fof(f450,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(unit_resulting_resolution,[],[f93,f98])).

fof(f449,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f93,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t1_filter_1.p',dt_k9_subset_1)).

fof(f5530,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v19_lattices(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl8_26 ),
    inference(resolution,[],[f727,f231])).

fof(f231,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK5(sK0,X9),X9)
      | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,X9),sK5(sK0,X9)),X9)
      | ~ r2_hidden(sK4(sK0,X9),X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | v19_lattices(X9,sK0) ) ),
    inference(subsumption_resolution,[],[f230,f118])).

fof(f230,plain,(
    ! [X9] :
      ( v1_xboole_0(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,X9),sK5(sK0,X9)),X9)
      | ~ r2_hidden(sK4(sK0,X9),X9)
      | ~ r2_hidden(sK5(sK0,X9),X9)
      | v19_lattices(X9,sK0) ) ),
    inference(subsumption_resolution,[],[f229,f96])).

fof(f229,plain,(
    ! [X9] :
      ( ~ l3_lattices(sK0)
      | v1_xboole_0(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,X9),sK5(sK0,X9)),X9)
      | ~ r2_hidden(sK4(sK0,X9),X9)
      | ~ r2_hidden(sK5(sK0,X9),X9)
      | v19_lattices(X9,sK0) ) ),
    inference(subsumption_resolution,[],[f206,f95])).

fof(f206,plain,(
    ! [X9] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v1_xboole_0(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,X9),sK5(sK0,X9)),X9)
      | ~ r2_hidden(sK4(sK0,X9),X9)
      | ~ r2_hidden(sK5(sK0,X9),X9)
      | v19_lattices(X9,sK0) ) ),
    inference(resolution,[],[f94,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k4_lattices(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | v19_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f5555,plain,
    ( ~ spl8_26
    | spl8_39 ),
    inference(avatar_contradiction_clause,[],[f5554])).

fof(f5554,plain,
    ( $false
    | ~ spl8_26
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f5527,f1750])).

fof(f1750,plain,
    ( ~ r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f1749])).

fof(f1749,plain,
    ( spl8_39
  <=> ~ r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f5527,plain,
    ( r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ spl8_26 ),
    inference(resolution,[],[f727,f135])).

fof(f5468,plain,
    ( spl8_28
    | spl8_24
    | spl8_5
    | spl8_7 ),
    inference(avatar_split_clause,[],[f5467,f155,f152,f720,f741])).

fof(f155,plain,
    ( spl8_7
  <=> ~ v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f5467,plain,
    ( r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f5466,f1401])).

fof(f5466,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f5465,f880])).

fof(f880,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f156,f371])).

fof(f156,plain,
    ( ~ v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f155])).

fof(f5465,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f5464,f96])).

fof(f5464,plain,
    ( ~ l3_lattices(sK0)
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f5463,f95])).

fof(f5463,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f984,f94])).

fof(f984,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5 ),
    inference(resolution,[],[f883,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k4_lattices(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(sK4(X0,X1),X1)
      | v19_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f5462,plain,
    ( spl8_26
    | spl8_24
    | spl8_5
    | spl8_7 ),
    inference(avatar_split_clause,[],[f5461,f155,f152,f720,f726])).

fof(f5461,plain,
    ( r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f5460,f1401])).

fof(f5460,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f5459,f880])).

fof(f5459,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f5458,f96])).

fof(f5458,plain,
    ( ~ l3_lattices(sK0)
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f5457,f95])).

fof(f5457,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f985,f94])).

fof(f985,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_5 ),
    inference(resolution,[],[f883,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k4_lattices(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(sK5(X0,X1),X1)
      | v19_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f5433,plain,
    ( ~ spl8_24
    | ~ spl8_32
    | ~ spl8_34
    | spl8_39 ),
    inference(avatar_contradiction_clause,[],[f5432])).

fof(f5432,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f5370,f3063])).

fof(f5370,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_39 ),
    inference(unit_resulting_resolution,[],[f95,f94,f96,f842,f92,f91,f93,f831,f1750,f185])).

fof(f185,plain,(
    ! [X6,X8,X7] :
      ( ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ r2_hidden(k4_lattices(X6,X7,X8),sK1)
      | r2_hidden(X8,sK1)
      | ~ v19_lattices(sK1,X6)
      | ~ v20_lattices(sK1,X6)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(resolution,[],[f90,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(k4_lattices(X0,X2,X3),X1)
      | r2_hidden(X3,X1)
      | v1_xboole_0(X1)
      | ~ v19_lattices(X1,X0)
      | ~ v20_lattices(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f5224,plain,
    ( ~ spl8_24
    | ~ spl8_32
    | ~ spl8_34
    | spl8_37 ),
    inference(avatar_contradiction_clause,[],[f5223])).

fof(f5223,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f5161,f3064])).

fof(f5161,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_37 ),
    inference(unit_resulting_resolution,[],[f95,f94,f96,f842,f88,f87,f89,f831,f1744,f164])).

fof(f164,plain,(
    ! [X6,X8,X7] :
      ( ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ r2_hidden(k4_lattices(X6,X7,X8),sK2)
      | r2_hidden(X8,sK2)
      | ~ v19_lattices(sK2,X6)
      | ~ v20_lattices(sK2,X6)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(resolution,[],[f86,f104])).

fof(f1744,plain,
    ( ~ r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f1743])).

fof(f1743,plain,
    ( spl8_37
  <=> ~ r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f1751,plain,
    ( ~ spl8_37
    | ~ spl8_39
    | spl8_27 ),
    inference(avatar_split_clause,[],[f1728,f723,f1749,f1743])).

fof(f723,plain,
    ( spl8_27
  <=> ~ r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f1728,plain,
    ( ~ r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),sK1)
    | ~ r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),sK2)
    | ~ spl8_27 ),
    inference(resolution,[],[f724,f133])).

fof(f724,plain,
    ( ~ r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f723])).

fof(f882,plain,
    ( spl8_7
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f881])).

fof(f881,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f880,f814])).

fof(f814,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f813])).

fof(f813,plain,
    ( spl8_30
  <=> v1_xboole_0(k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f872,plain,
    ( spl8_30
    | spl8_34
    | spl8_5 ),
    inference(avatar_split_clause,[],[f871,f152,f841,f813])).

fof(f871,plain,
    ( m1_subset_1(sK4(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f870,f371])).

fof(f870,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f869,f395])).

fof(f395,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f370,f371])).

fof(f370,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f89,f99])).

fof(f869,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f868,f371])).

fof(f868,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f696,f371])).

fof(f696,plain,
    ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f695,f96])).

fof(f695,plain,
    ( ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f694,f95])).

fof(f694,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f649,f94])).

fof(f649,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(resolution,[],[f153,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | v19_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f867,plain,
    ( spl8_30
    | spl8_32
    | spl8_5 ),
    inference(avatar_split_clause,[],[f866,f152,f830,f813])).

fof(f866,plain,
    ( m1_subset_1(sK5(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f865,f371])).

fof(f865,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f864,f395])).

fof(f864,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f863,f371])).

fof(f863,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f703,f371])).

fof(f703,plain,
    ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f702,f96])).

fof(f702,plain,
    ( ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f701,f95])).

fof(f701,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f648,f94])).

fof(f648,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(resolution,[],[f153,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v19_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f843,plain,
    ( spl8_30
    | spl8_34
    | spl8_3 ),
    inference(avatar_split_clause,[],[f836,f146,f841,f813])).

fof(f146,plain,
    ( spl8_3
  <=> ~ v20_lattices(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f836,plain,
    ( m1_subset_1(sK4(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f835,f371])).

fof(f835,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f834,f395])).

fof(f834,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f833,f371])).

fof(f833,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f756,f371])).

fof(f756,plain,
    ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f755,f96])).

fof(f755,plain,
    ( ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f754,f95])).

fof(f754,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f620,f94])).

fof(f620,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(resolution,[],[f147,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | v20_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f147,plain,
    ( ~ v20_lattices(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f832,plain,
    ( spl8_30
    | spl8_32
    | spl8_3 ),
    inference(avatar_split_clause,[],[f825,f146,f830,f813])).

fof(f825,plain,
    ( m1_subset_1(sK5(sK0,k3_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f824,f371])).

fof(f824,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f823,f395])).

fof(f823,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f822,f371])).

fof(f822,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f763,f371])).

fof(f763,plain,
    ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f762,f96])).

fof(f762,plain,
    ( ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f761,f95])).

fof(f761,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f619,f94])).

fof(f619,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(resolution,[],[f147,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v20_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f821,plain,
    ( spl8_30
    | spl8_24
    | spl8_26
    | spl8_3 ),
    inference(avatar_split_clause,[],[f820,f146,f726,f720,f813])).

fof(f820,plain,
    ( r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f819,f371])).

fof(f819,plain,
    ( r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f818,f371])).

fof(f818,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f817,f395])).

fof(f817,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f816,f371])).

fof(f816,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f770,f371])).

fof(f770,plain,
    ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f769,f96])).

fof(f769,plain,
    ( ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f768,f95])).

fof(f768,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f618,f94])).

fof(f618,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(resolution,[],[f147,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k4_lattices(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(sK5(X0,X1),X1)
      | v20_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f815,plain,
    ( spl8_30
    | spl8_24
    | spl8_28
    | spl8_3 ),
    inference(avatar_split_clause,[],[f808,f146,f741,f720,f813])).

fof(f808,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f807,f371])).

fof(f807,plain,
    ( r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f806,f371])).

fof(f806,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f805,f395])).

fof(f805,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k3_xboole_0(sK1,sK2))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f804,f371])).

fof(f804,plain,
    ( v1_xboole_0(k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f779,f371])).

fof(f779,plain,
    ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f778,f96])).

fof(f778,plain,
    ( ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f777,f95])).

fof(f777,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f617,f94])).

fof(f617,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(resolution,[],[f147,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k4_lattices(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(sK4(X0,X1),X1)
      | v20_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f803,plain,
    ( ~ spl8_25
    | ~ spl8_29
    | ~ spl8_27
    | spl8_3 ),
    inference(avatar_split_clause,[],[f802,f146,f723,f738,f717])).

fof(f802,plain,
    ( ~ r2_hidden(sK5(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f801,f371])).

fof(f801,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f800,f371])).

fof(f800,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k3_xboole_0(sK1,sK2)),sK5(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f799,f371])).

fof(f799,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f798,f395])).

fof(f798,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f797,f371])).

fof(f797,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f788,f118])).

fof(f788,plain,
    ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f787,f96])).

fof(f787,plain,
    ( ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f786,f95])).

fof(f786,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f616,f94])).

fof(f616,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k4_lattices(sK0,sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r2_hidden(sK5(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl8_3 ),
    inference(resolution,[],[f147,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k4_lattices(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | v20_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f693,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f692])).

fof(f692,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f691,f89])).

fof(f691,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f681,f395])).

fof(f681,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_1 ),
    inference(superposition,[],[f141,f98])).

fof(f141,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_1
  <=> ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f160,plain,
    ( ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f85,f158,f152,f146,f140])).

fof(f85,plain,
    ( v1_xboole_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ v19_lattices(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v20_lattices(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
