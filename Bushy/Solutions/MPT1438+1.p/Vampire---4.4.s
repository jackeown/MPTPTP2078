%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t33_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:09 EDT 2019

% Result     : Theorem 38.98s
% Output     : Refutation 38.98s
% Verified   : 
% Statistics : Number of formulae       :  319 ( 774 expanded)
%              Number of leaves         :   61 ( 284 expanded)
%              Depth                    :   33
%              Number of atoms          : 1245 (2868 expanded)
%              Number of equality atoms :  147 ( 400 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f157,f164,f208,f215,f223,f230,f238,f245,f267,f272,f279,f286,f308,f315,f2010,f2016,f5272,f6886,f33150,f66225,f66336,f66663,f66868,f67840,f72505,f75673,f87278,f87361,f87406,f89743,f89785,f89981,f93322,f93347,f96352,f96471,f97220])).

fof(f97220,plain,
    ( spl15_31
    | spl15_1881
    | ~ spl15_1888 ),
    inference(avatar_contradiction_clause,[],[f97219])).

fof(f97219,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_1881
    | ~ spl15_1888 ),
    inference(subsumption_resolution,[],[f97218,f87271])).

fof(f87271,plain,
    ( m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1888 ),
    inference(avatar_component_clause,[],[f87270])).

fof(f87270,plain,
    ( spl15_1888
  <=> m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1888])])).

fof(f97218,plain,
    ( ~ m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_31
    | ~ spl15_1881 ),
    inference(subsumption_resolution,[],[f97215,f301])).

fof(f301,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_31 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl15_31
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_31])])).

fof(f97215,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1881 ),
    inference(resolution,[],[f84328,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',t2_subset)).

fof(f84328,plain,
    ( ~ r2_hidden(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1881 ),
    inference(avatar_component_clause,[],[f84327])).

fof(f84327,plain,
    ( spl15_1881
  <=> ~ r2_hidden(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1881])])).

fof(f96471,plain,
    ( ~ spl15_9
    | ~ spl15_10
    | spl15_141 ),
    inference(avatar_split_clause,[],[f96157,f1848,f203,f200])).

fof(f200,plain,
    ( spl15_9
  <=> u1_struct_0(sK0) != k2_relat_1(k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_9])])).

fof(f203,plain,
    ( spl15_10
  <=> k1_relat_1(k8_filter_1(sK0)) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_10])])).

fof(f1848,plain,
    ( spl15_141
  <=> k1_relat_1(k8_filter_1(sK0)) != k2_relat_1(k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_141])])).

fof(f96157,plain,
    ( u1_struct_0(sK0) != k2_relat_1(k8_filter_1(sK0))
    | ~ spl15_10
    | ~ spl15_141 ),
    inference(forward_demodulation,[],[f1849,f204])).

fof(f204,plain,
    ( k1_relat_1(k8_filter_1(sK0)) = u1_struct_0(sK0)
    | ~ spl15_10 ),
    inference(avatar_component_clause,[],[f203])).

fof(f1849,plain,
    ( k1_relat_1(k8_filter_1(sK0)) != k2_relat_1(k8_filter_1(sK0))
    | ~ spl15_141 ),
    inference(avatar_component_clause,[],[f1848])).

fof(f96352,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_10
    | ~ spl15_18
    | spl15_31
    | spl15_143
    | ~ spl15_1892 ),
    inference(avatar_contradiction_clause,[],[f96351])).

fof(f96351,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_10
    | ~ spl15_18
    | ~ spl15_31
    | ~ spl15_143
    | ~ spl15_1892 ),
    inference(subsumption_resolution,[],[f90166,f96330])).

fof(f96330,plain,
    ( k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))) != k4_tarski(sK2(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK0),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK0))
    | ~ spl15_10
    | ~ spl15_143 ),
    inference(forward_demodulation,[],[f1855,f204])).

fof(f1855,plain,
    ( k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))) != k4_tarski(sK2(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0))
    | ~ spl15_143 ),
    inference(avatar_component_clause,[],[f1854])).

fof(f1854,plain,
    ( spl15_143
  <=> k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))) != k4_tarski(sK2(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_143])])).

fof(f90166,plain,
    ( k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))) = k4_tarski(sK2(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK0),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31
    | ~ spl15_1892 ),
    inference(resolution,[],[f87357,f380])).

fof(f380,plain,
    ( ! [X4] :
        ( ~ sP6(X4,k8_filter_1(sK0))
        | k4_tarski(sK7(k8_filter_1(sK0),X4),X4) = k4_tarski(sK2(k4_tarski(sK7(k8_filter_1(sK0),X4),X4),sK0),sK3(k4_tarski(sK7(k8_filter_1(sK0),X4),X4),sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(resolution,[],[f371,f113])).

fof(f113,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',d5_relat_1)).

fof(f371,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k8_filter_1(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0 )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k8_filter_1(sK0))
        | ~ r2_hidden(X0,k8_filter_1(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0 )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(forward_demodulation,[],[f369,f237])).

fof(f237,plain,
    ( k8_filter_1(sK0) = a_1_0_filter_1(sK0)
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl15_18
  <=> k8_filter_1(sK0) = a_1_0_filter_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f369,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k8_filter_1(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0
        | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(subsumption_resolution,[],[f368,f149])).

fof(f149,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl15_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f368,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k8_filter_1(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(subsumption_resolution,[],[f367,f163])).

fof(f163,plain,
    ( l3_lattices(sK0)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl15_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k8_filter_1(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(subsumption_resolution,[],[f365,f156])).

fof(f156,plain,
    ( v10_lattices(sK0)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl15_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k8_filter_1(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0
        | ~ v10_lattices(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(resolution,[],[f364,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X1))
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',fraenkel_a_1_0_filter_1)).

fof(f364,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0))
        | ~ r2_hidden(X0,k8_filter_1(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0 )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k8_filter_1(sK0))
        | ~ r2_hidden(X0,k8_filter_1(sK0))
        | ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0 )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(forward_demodulation,[],[f362,f237])).

fof(f362,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k8_filter_1(sK0))
        | ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0
        | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_31 ),
    inference(subsumption_resolution,[],[f361,f149])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k8_filter_1(sK0))
        | ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_31 ),
    inference(subsumption_resolution,[],[f360,f163])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k8_filter_1(sK0))
        | ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_31 ),
    inference(subsumption_resolution,[],[f358,f156])).

fof(f358,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k8_filter_1(sK0))
        | ~ m1_subset_1(sK2(X0,sK0),u1_struct_0(sK0))
        | k4_tarski(sK2(X0,sK0),sK3(X0,sK0)) = X0
        | ~ v10_lattices(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_31 ),
    inference(resolution,[],[f340,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X1))
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f340,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3(X1,sK0),u1_struct_0(sK0))
        | ~ r2_hidden(X1,k8_filter_1(sK0))
        | ~ m1_subset_1(sK2(X1,sK0),u1_struct_0(sK0))
        | k4_tarski(sK2(X1,sK0),sK3(X1,sK0)) = X1 )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_31 ),
    inference(subsumption_resolution,[],[f294,f301])).

fof(f294,plain,
    ( ! [X1] :
        ( k4_tarski(sK2(X1,sK0),sK3(X1,sK0)) = X1
        | ~ r2_hidden(X1,k8_filter_1(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(X1,sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X1,sK0),u1_struct_0(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,
    ( ! [X1] :
        ( k4_tarski(sK2(X1,sK0),sK3(X1,sK0)) = X1
        | ~ r2_hidden(X1,k8_filter_1(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(X1,sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X1,sK0),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(superposition,[],[f180,f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k4_tarski(X2,X3) = k1_domain_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',redefinition_k1_domain_1)).

fof(f180,plain,
    ( ! [X0] :
        ( k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2(X0,sK0),sK3(X0,sK0)) = X0
        | ~ r2_hidden(X0,k8_filter_1(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(forward_demodulation,[],[f179,f177])).

fof(f177,plain,
    ( k8_filter_1(sK0) = a_1_0_filter_1(sK0)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f176,f149])).

fof(f176,plain,
    ( v2_struct_0(sK0)
    | k8_filter_1(sK0) = a_1_0_filter_1(sK0)
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f167,f156])).

fof(f167,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | k8_filter_1(sK0) = a_1_0_filter_1(sK0)
    | ~ spl15_4 ),
    inference(resolution,[],[f163,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | k8_filter_1(X0) = a_1_0_filter_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k8_filter_1(X0) = a_1_0_filter_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',d8_filter_1)).

fof(f179,plain,
    ( ! [X0] :
        ( k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2(X0,sK0),sK3(X0,sK0)) = X0
        | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f178,f149])).

fof(f178,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2(X0,sK0),sK3(X0,sK0)) = X0
        | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) )
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f168,f156])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2(X0,sK0),sK3(X0,sK0)) = X0
        | ~ r2_hidden(X0,a_1_0_filter_1(sK0)) )
    | ~ spl15_4 ),
    inference(resolution,[],[f163,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK2(X0,X1),sK3(X0,X1)) = X0
      | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f87357,plain,
    ( sP6(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),k8_filter_1(sK0))
    | ~ spl15_1892 ),
    inference(avatar_component_clause,[],[f87356])).

fof(f87356,plain,
    ( spl15_1892
  <=> sP6(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1892])])).

fof(f93347,plain,
    ( k1_relat_1(k8_filter_1(sK0)) != u1_struct_0(sK0)
    | k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))) != k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0))
    | k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))) = k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK0)) ),
    introduced(theory_axiom,[])).

fof(f93322,plain,
    ( ~ spl15_10
    | ~ spl15_20
    | ~ spl15_1880
    | ~ spl15_1892 ),
    inference(avatar_contradiction_clause,[],[f93321])).

fof(f93321,plain,
    ( $false
    | ~ spl15_10
    | ~ spl15_20
    | ~ spl15_1880
    | ~ spl15_1892 ),
    inference(global_subsumption,[],[f79,f204,f90178,f93320])).

fof(f93320,plain,
    ( u1_struct_0(sK0) = k3_relat_1(k8_filter_1(sK0))
    | ~ spl15_10
    | ~ spl15_20
    | ~ spl15_1880
    | ~ spl15_1892 ),
    inference(forward_demodulation,[],[f93319,f101])).

fof(f101,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',idempotence_k2_xboole_0)).

fof(f93319,plain,
    ( k3_relat_1(k8_filter_1(sK0)) = k2_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl15_10
    | ~ spl15_20
    | ~ spl15_1880
    | ~ spl15_1892 ),
    inference(forward_demodulation,[],[f93318,f204])).

fof(f93318,plain,
    ( k3_relat_1(k8_filter_1(sK0)) = k2_xboole_0(k1_relat_1(k8_filter_1(sK0)),u1_struct_0(sK0))
    | ~ spl15_20
    | ~ spl15_1880
    | ~ spl15_1892 ),
    inference(forward_demodulation,[],[f244,f90178])).

fof(f244,plain,
    ( k3_relat_1(k8_filter_1(sK0)) = k2_xboole_0(k1_relat_1(k8_filter_1(sK0)),k2_relat_1(k8_filter_1(sK0)))
    | ~ spl15_20 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl15_20
  <=> k3_relat_1(k8_filter_1(sK0)) = k2_xboole_0(k1_relat_1(k8_filter_1(sK0)),k2_relat_1(k8_filter_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f90178,plain,
    ( u1_struct_0(sK0) = k2_relat_1(k8_filter_1(sK0))
    | ~ spl15_1880
    | ~ spl15_1892 ),
    inference(subsumption_resolution,[],[f90165,f84331])).

fof(f84331,plain,
    ( r2_hidden(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1880 ),
    inference(avatar_component_clause,[],[f84330])).

fof(f84330,plain,
    ( spl15_1880
  <=> r2_hidden(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1880])])).

fof(f90165,plain,
    ( ~ r2_hidden(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_relat_1(k8_filter_1(sK0))
    | ~ spl15_1892 ),
    inference(resolution,[],[f87357,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ sP6(sK5(X0,X1),X0)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,
    ( k1_relat_1(k8_filter_1(sK0)) != u1_struct_0(sK0)
    | u1_struct_0(sK0) != k2_relat_1(k8_filter_1(sK0))
    | u1_struct_0(sK0) != k3_relat_1(k8_filter_1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ( u1_struct_0(X0) != k3_relat_1(k8_filter_1(X0))
        | u1_struct_0(X0) != k2_relat_1(k8_filter_1(X0))
        | k1_relat_1(k8_filter_1(X0)) != u1_struct_0(X0) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ( u1_struct_0(X0) != k3_relat_1(k8_filter_1(X0))
        | u1_struct_0(X0) != k2_relat_1(k8_filter_1(X0))
        | k1_relat_1(k8_filter_1(X0)) != u1_struct_0(X0) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( u1_struct_0(X0) = k3_relat_1(k8_filter_1(X0))
          & u1_struct_0(X0) = k2_relat_1(k8_filter_1(X0))
          & k1_relat_1(k8_filter_1(X0)) = u1_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( u1_struct_0(X0) = k3_relat_1(k8_filter_1(X0))
        & u1_struct_0(X0) = k2_relat_1(k8_filter_1(X0))
        & k1_relat_1(k8_filter_1(X0)) = u1_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',t33_filter_1)).

fof(f89981,plain,
    ( ~ spl15_1889
    | ~ spl15_22
    | ~ spl15_1922 ),
    inference(avatar_split_clause,[],[f89903,f89741,f247,f87267])).

fof(f87267,plain,
    ( spl15_1889
  <=> ~ m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1889])])).

fof(f247,plain,
    ( spl15_22
  <=> ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r3_lattices(sK0,X8,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).

fof(f89741,plain,
    ( spl15_1922
  <=> ! [X0] :
        ( ~ r3_lattices(sK0,X0,sK5(k8_filter_1(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1922])])).

fof(f89903,plain,
    ( ~ m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_22
    | ~ spl15_1922 ),
    inference(duplicate_literal_removal,[],[f89900])).

fof(f89900,plain,
    ( ~ m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_22
    | ~ spl15_1922 ),
    inference(resolution,[],[f89742,f248])).

fof(f248,plain,
    ( ! [X8] :
        ( r3_lattices(sK0,X8,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl15_22 ),
    inference(avatar_component_clause,[],[f247])).

fof(f89742,plain,
    ( ! [X0] :
        ( ~ r3_lattices(sK0,X0,sK5(k8_filter_1(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_1922 ),
    inference(avatar_component_clause,[],[f89741])).

fof(f89785,plain,
    ( ~ spl15_1880
    | spl15_1889 ),
    inference(avatar_contradiction_clause,[],[f89784])).

fof(f89784,plain,
    ( $false
    | ~ spl15_1880
    | ~ spl15_1889 ),
    inference(subsumption_resolution,[],[f89783,f84331])).

fof(f89783,plain,
    ( ~ r2_hidden(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1889 ),
    inference(resolution,[],[f87268,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',t1_subset)).

fof(f87268,plain,
    ( ~ m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1889 ),
    inference(avatar_component_clause,[],[f87267])).

fof(f89743,plain,
    ( ~ spl15_1889
    | spl15_1922
    | ~ spl15_32
    | spl15_1893 ),
    inference(avatar_split_clause,[],[f88735,f87359,f306,f89741,f87267])).

fof(f306,plain,
    ( spl15_32
  <=> ! [X1,X2] :
        ( r2_hidden(k4_tarski(X1,X2),k8_filter_1(sK0))
        | ~ r3_lattices(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_32])])).

fof(f87359,plain,
    ( spl15_1893
  <=> ~ sP6(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1893])])).

fof(f88735,plain,
    ( ! [X0] :
        ( ~ r3_lattices(sK0,X0,sK5(k8_filter_1(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_32
    | ~ spl15_1893 ),
    inference(resolution,[],[f87402,f307])).

fof(f307,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(X1,X2),k8_filter_1(sK0))
        | ~ r3_lattices(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl15_32 ),
    inference(avatar_component_clause,[],[f306])).

fof(f87402,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK5(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0))
    | ~ spl15_1893 ),
    inference(resolution,[],[f87360,f114])).

fof(f114,plain,(
    ! [X2,X0,X3] :
      ( sP6(X2,X0)
      | ~ r2_hidden(k4_tarski(X3,X2),X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f87360,plain,
    ( ~ sP6(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),k8_filter_1(sK0))
    | ~ spl15_1893 ),
    inference(avatar_component_clause,[],[f87359])).

fof(f87406,plain,
    ( spl15_1880
    | spl15_9
    | spl15_1893 ),
    inference(avatar_split_clause,[],[f87404,f87359,f200,f84330])).

fof(f87404,plain,
    ( r2_hidden(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_9
    | ~ spl15_1893 ),
    inference(subsumption_resolution,[],[f87401,f201])).

fof(f201,plain,
    ( u1_struct_0(sK0) != k2_relat_1(k8_filter_1(sK0))
    | ~ spl15_9 ),
    inference(avatar_component_clause,[],[f200])).

fof(f87401,plain,
    ( r2_hidden(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_relat_1(k8_filter_1(sK0))
    | ~ spl15_1893 ),
    inference(resolution,[],[f87360,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( sP6(sK5(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f87361,plain,
    ( ~ spl15_1893
    | spl15_1891 ),
    inference(avatar_split_clause,[],[f87314,f87276,f87359])).

fof(f87276,plain,
    ( spl15_1891
  <=> ~ r2_hidden(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1891])])).

fof(f87314,plain,
    ( ~ sP6(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),k8_filter_1(sK0))
    | ~ spl15_1891 ),
    inference(resolution,[],[f87277,f113])).

fof(f87277,plain,
    ( ~ r2_hidden(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0))
    | ~ spl15_1891 ),
    inference(avatar_component_clause,[],[f87276])).

fof(f87278,plain,
    ( spl15_1888
    | ~ spl15_1891
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_1588 ),
    inference(avatar_split_clause,[],[f75714,f75671,f236,f162,f155,f148,f87276,f87270])).

fof(f75671,plain,
    ( spl15_1588
  <=> sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK0) = sK5(k8_filter_1(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1588])])).

fof(f75714,plain,
    ( ~ r2_hidden(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),k8_filter_1(sK0))
    | m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_1588 ),
    inference(forward_demodulation,[],[f75713,f237])).

fof(f75713,plain,
    ( m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),a_1_0_filter_1(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_1588 ),
    inference(subsumption_resolution,[],[f75712,f149])).

fof(f75712,plain,
    ( m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),a_1_0_filter_1(sK0))
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_1588 ),
    inference(subsumption_resolution,[],[f75711,f163])).

fof(f75711,plain,
    ( m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),a_1_0_filter_1(sK0))
    | ~ spl15_2
    | ~ spl15_1588 ),
    inference(subsumption_resolution,[],[f75703,f156])).

fof(f75703,plain,
    ( m1_subset_1(sK5(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),a_1_0_filter_1(sK0))
    | ~ spl15_1588 ),
    inference(superposition,[],[f107,f75672])).

fof(f75672,plain,
    ( sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK0) = sK5(k8_filter_1(sK0),u1_struct_0(sK0))
    | ~ spl15_1588 ),
    inference(avatar_component_clause,[],[f75671])).

fof(f75673,plain,
    ( spl15_1588
    | ~ spl15_1524 ),
    inference(avatar_split_clause,[],[f73969,f71893,f75671])).

fof(f71893,plain,
    ( spl15_1524
  <=> k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))) = k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1524])])).

fof(f73969,plain,
    ( sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK0) = sK5(k8_filter_1(sK0),u1_struct_0(sK0))
    | ~ spl15_1524 ),
    inference(equality_resolution,[],[f71899])).

fof(f71899,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0)))
        | sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK0) = X5 )
    | ~ spl15_1524 ),
    inference(superposition,[],[f131,f71894])).

fof(f71894,plain,
    ( k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))) = k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK5(k8_filter_1(sK0),u1_struct_0(sK0))),sK0))
    | ~ spl15_1524 ),
    inference(avatar_component_clause,[],[f71893])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',t33_zfmisc_1)).

fof(f72505,plain,
    ( spl15_10
    | spl15_1461
    | spl15_1465 ),
    inference(avatar_split_clause,[],[f68777,f66334,f66214,f203])).

fof(f66214,plain,
    ( spl15_1461
  <=> ~ m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1461])])).

fof(f66334,plain,
    ( spl15_1465
  <=> ~ sP9(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1465])])).

fof(f68777,plain,
    ( k1_relat_1(k8_filter_1(sK0)) = u1_struct_0(sK0)
    | ~ spl15_1461
    | ~ spl15_1465 ),
    inference(subsumption_resolution,[],[f66958,f68735])).

fof(f68735,plain,
    ( ~ r2_hidden(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1461 ),
    inference(resolution,[],[f66215,f104])).

fof(f66215,plain,
    ( ~ m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1461 ),
    inference(avatar_component_clause,[],[f66214])).

fof(f66958,plain,
    ( r2_hidden(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | k1_relat_1(k8_filter_1(sK0)) = u1_struct_0(sK0)
    | ~ spl15_1465 ),
    inference(resolution,[],[f66335,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( sP9(sK8(X0,X1),X0)
      | r2_hidden(sK8(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',d4_relat_1)).

fof(f66335,plain,
    ( ~ sP9(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),k8_filter_1(sK0))
    | ~ spl15_1465 ),
    inference(avatar_component_clause,[],[f66334])).

fof(f67840,plain,
    ( ~ spl15_22
    | ~ spl15_32
    | ~ spl15_1460
    | spl15_1465 ),
    inference(avatar_contradiction_clause,[],[f67839])).

fof(f67839,plain,
    ( $false
    | ~ spl15_22
    | ~ spl15_32
    | ~ spl15_1460
    | ~ spl15_1465 ),
    inference(subsumption_resolution,[],[f67838,f66218])).

fof(f66218,plain,
    ( m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1460 ),
    inference(avatar_component_clause,[],[f66217])).

fof(f66217,plain,
    ( spl15_1460
  <=> m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1460])])).

fof(f67838,plain,
    ( ~ m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_22
    | ~ spl15_32
    | ~ spl15_1460
    | ~ spl15_1465 ),
    inference(duplicate_literal_removal,[],[f67835])).

fof(f67835,plain,
    ( ~ m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_22
    | ~ spl15_32
    | ~ spl15_1460
    | ~ spl15_1465 ),
    inference(resolution,[],[f67675,f248])).

fof(f67675,plain,
    ( ! [X0] :
        ( ~ r3_lattices(sK0,sK8(k8_filter_1(sK0),u1_struct_0(sK0)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_32
    | ~ spl15_1460
    | ~ spl15_1465 ),
    inference(subsumption_resolution,[],[f67672,f66218])).

fof(f67672,plain,
    ( ! [X0] :
        ( ~ r3_lattices(sK0,sK8(k8_filter_1(sK0),u1_struct_0(sK0)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | ~ spl15_32
    | ~ spl15_1465 ),
    inference(resolution,[],[f66959,f307])).

fof(f66959,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),X0),k8_filter_1(sK0))
    | ~ spl15_1465 ),
    inference(resolution,[],[f66335,f120])).

fof(f120,plain,(
    ! [X2,X0,X3] :
      ( sP9(X2,X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f66868,plain,
    ( spl15_31
    | spl15_1455
    | ~ spl15_1460 ),
    inference(avatar_contradiction_clause,[],[f66867])).

fof(f66867,plain,
    ( $false
    | ~ spl15_31
    | ~ spl15_1455
    | ~ spl15_1460 ),
    inference(subsumption_resolution,[],[f66866,f66218])).

fof(f66866,plain,
    ( ~ m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_31
    | ~ spl15_1455 ),
    inference(subsumption_resolution,[],[f66863,f301])).

fof(f66863,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1455 ),
    inference(resolution,[],[f65842,f105])).

fof(f65842,plain,
    ( ~ r2_hidden(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1455 ),
    inference(avatar_component_clause,[],[f65841])).

fof(f65841,plain,
    ( spl15_1455
  <=> ~ r2_hidden(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1455])])).

fof(f66663,plain,
    ( ~ spl15_1455
    | spl15_11
    | ~ spl15_1464 ),
    inference(avatar_split_clause,[],[f66634,f66331,f206,f65841])).

fof(f206,plain,
    ( spl15_11
  <=> k1_relat_1(k8_filter_1(sK0)) != u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_11])])).

fof(f66331,plain,
    ( spl15_1464
  <=> sP9(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1464])])).

fof(f66634,plain,
    ( ~ r2_hidden(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_11
    | ~ spl15_1464 ),
    inference(subsumption_resolution,[],[f66623,f207])).

fof(f207,plain,
    ( k1_relat_1(k8_filter_1(sK0)) != u1_struct_0(sK0)
    | ~ spl15_11 ),
    inference(avatar_component_clause,[],[f206])).

fof(f66623,plain,
    ( ~ r2_hidden(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | k1_relat_1(k8_filter_1(sK0)) = u1_struct_0(sK0)
    | ~ spl15_1464 ),
    inference(resolution,[],[f66332,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ sP9(sK8(X0,X1),X0)
      | ~ r2_hidden(sK8(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f66332,plain,
    ( sP9(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),k8_filter_1(sK0))
    | ~ spl15_1464 ),
    inference(avatar_component_clause,[],[f66331])).

fof(f66336,plain,
    ( ~ spl15_1465
    | spl15_1463 ),
    inference(avatar_split_clause,[],[f66277,f66223,f66334])).

fof(f66223,plain,
    ( spl15_1463
  <=> ~ r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1463])])).

fof(f66277,plain,
    ( ~ sP9(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),k8_filter_1(sK0))
    | ~ spl15_1463 ),
    inference(resolution,[],[f66224,f119])).

fof(f119,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK10(X0,X2)),X0)
      | ~ sP9(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f66224,plain,
    ( ~ r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),k8_filter_1(sK0))
    | ~ spl15_1463 ),
    inference(avatar_component_clause,[],[f66223])).

fof(f66225,plain,
    ( spl15_1460
    | ~ spl15_1463
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_868 ),
    inference(avatar_split_clause,[],[f35350,f33148,f236,f162,f155,f148,f66223,f66217])).

fof(f33148,plain,
    ( spl15_868
  <=> sK2(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0) = sK8(k8_filter_1(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_868])])).

fof(f35350,plain,
    ( ~ r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),k8_filter_1(sK0))
    | m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_868 ),
    inference(forward_demodulation,[],[f35349,f237])).

fof(f35349,plain,
    ( m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),a_1_0_filter_1(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_868 ),
    inference(subsumption_resolution,[],[f35348,f149])).

fof(f35348,plain,
    ( m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),a_1_0_filter_1(sK0))
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_868 ),
    inference(subsumption_resolution,[],[f35347,f163])).

fof(f35347,plain,
    ( m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),a_1_0_filter_1(sK0))
    | ~ spl15_2
    | ~ spl15_868 ),
    inference(subsumption_resolution,[],[f35340,f156])).

fof(f35340,plain,
    ( m1_subset_1(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),a_1_0_filter_1(sK0))
    | ~ spl15_868 ),
    inference(superposition,[],[f106,f33149])).

fof(f33149,plain,
    ( sK2(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0) = sK8(k8_filter_1(sK0),u1_struct_0(sK0))
    | ~ spl15_868 ),
    inference(avatar_component_clause,[],[f33148])).

fof(f33150,plain,
    ( spl15_868
    | ~ spl15_324 ),
    inference(avatar_split_clause,[],[f18604,f6884,f33148])).

fof(f6884,plain,
    ( spl15_324
  <=> k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))) = k4_tarski(sK2(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0),sK3(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_324])])).

fof(f18604,plain,
    ( sK2(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0) = sK8(k8_filter_1(sK0),u1_struct_0(sK0))
    | ~ spl15_324 ),
    inference(equality_resolution,[],[f7981])).

fof(f7981,plain,
    ( ! [X0,X1] :
        ( k4_tarski(X0,X1) != k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0))))
        | sK2(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0) = X0 )
    | ~ spl15_324 ),
    inference(superposition,[],[f130,f6885])).

fof(f6885,plain,
    ( k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))) = k4_tarski(sK2(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0),sK3(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0))
    | ~ spl15_324 ),
    inference(avatar_component_clause,[],[f6884])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f6886,plain,
    ( spl15_324
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | spl15_11
    | ~ spl15_18
    | ~ spl15_22
    | spl15_31
    | ~ spl15_32 ),
    inference(avatar_split_clause,[],[f3338,f306,f300,f247,f236,f206,f162,f155,f148,f6884])).

fof(f3338,plain,
    ( k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))) = k4_tarski(sK2(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0),sK3(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_11
    | ~ spl15_18
    | ~ spl15_22
    | ~ spl15_31
    | ~ spl15_32 ),
    inference(global_subsumption,[],[f1307,f207])).

fof(f1307,plain,
    ( k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))) = k4_tarski(sK2(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0),sK3(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0))
    | k1_relat_1(k8_filter_1(sK0)) = u1_struct_0(sK0)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_22
    | ~ spl15_31
    | ~ spl15_32 ),
    inference(duplicate_literal_removal,[],[f1303])).

fof(f1303,plain,
    ( k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))) = k4_tarski(sK2(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0),sK3(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0))
    | k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))) = k4_tarski(sK2(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0),sK3(k4_tarski(sK8(k8_filter_1(sK0),u1_struct_0(sK0)),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),u1_struct_0(sK0)))),sK0))
    | k1_relat_1(k8_filter_1(sK0)) = u1_struct_0(sK0)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_22
    | ~ spl15_31
    | ~ spl15_32 ),
    inference(resolution,[],[f1207,f605])).

fof(f605,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(k8_filter_1(sK0),X0),X0)
        | k4_tarski(sK8(k8_filter_1(sK0),X0),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),X0))) = k4_tarski(sK2(k4_tarski(sK8(k8_filter_1(sK0),X0),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),X0))),sK0),sK3(k4_tarski(sK8(k8_filter_1(sK0),X0),sK10(k8_filter_1(sK0),sK8(k8_filter_1(sK0),X0))),sK0))
        | k1_relat_1(k8_filter_1(sK0)) = X0 )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(resolution,[],[f383,f123])).

fof(f383,plain,
    ( ! [X7] :
        ( ~ sP9(X7,k8_filter_1(sK0))
        | k4_tarski(X7,sK10(k8_filter_1(sK0),X7)) = k4_tarski(sK2(k4_tarski(X7,sK10(k8_filter_1(sK0),X7)),sK0),sK3(k4_tarski(X7,sK10(k8_filter_1(sK0),X7)),sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(resolution,[],[f371,f119])).

fof(f1207,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | k4_tarski(X0,sK10(k8_filter_1(sK0),X0)) = k4_tarski(sK2(k4_tarski(X0,sK10(k8_filter_1(sK0),X0)),sK0),sK3(k4_tarski(X0,sK10(k8_filter_1(sK0),X0)),sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_22
    | ~ spl15_31
    | ~ spl15_32 ),
    inference(resolution,[],[f1105,f104])).

fof(f1105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_tarski(X0,sK10(k8_filter_1(sK0),X0)) = k4_tarski(sK2(k4_tarski(X0,sK10(k8_filter_1(sK0),X0)),sK0),sK3(k4_tarski(X0,sK10(k8_filter_1(sK0),X0)),sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_22
    | ~ spl15_31
    | ~ spl15_32 ),
    inference(duplicate_literal_removal,[],[f1099])).

fof(f1099,plain,
    ( ! [X0] :
        ( k4_tarski(X0,sK10(k8_filter_1(sK0),X0)) = k4_tarski(sK2(k4_tarski(X0,sK10(k8_filter_1(sK0),X0)),sK0),sK3(k4_tarski(X0,sK10(k8_filter_1(sK0),X0)),sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_22
    | ~ spl15_31
    | ~ spl15_32 ),
    inference(resolution,[],[f676,f248])).

fof(f676,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,X0,X1)
        | k4_tarski(X0,sK10(k8_filter_1(sK0),X0)) = k4_tarski(sK2(k4_tarski(X0,sK10(k8_filter_1(sK0),X0)),sK0),sK3(k4_tarski(X0,sK10(k8_filter_1(sK0),X0)),sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31
    | ~ spl15_32 ),
    inference(resolution,[],[f606,f307])).

fof(f606,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X2),k8_filter_1(sK0))
        | k4_tarski(X1,sK10(k8_filter_1(sK0),X1)) = k4_tarski(sK2(k4_tarski(X1,sK10(k8_filter_1(sK0),X1)),sK0),sK3(k4_tarski(X1,sK10(k8_filter_1(sK0),X1)),sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_31 ),
    inference(resolution,[],[f383,f120])).

fof(f5272,plain,
    ( spl15_248
    | ~ spl15_142 ),
    inference(avatar_split_clause,[],[f5248,f1857,f5270])).

fof(f5270,plain,
    ( spl15_248
  <=> k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))) = k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_248])])).

fof(f1857,plain,
    ( spl15_142
  <=> k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))) = k4_tarski(sK2(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_142])])).

fof(f5248,plain,
    ( k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))) = k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0))
    | ~ spl15_142 ),
    inference(backward_demodulation,[],[f5247,f1858])).

fof(f1858,plain,
    ( k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))) = k4_tarski(sK2(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0),sK3(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0))
    | ~ spl15_142 ),
    inference(avatar_component_clause,[],[f1857])).

fof(f5247,plain,
    ( sK2(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0) = sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0))))
    | ~ spl15_142 ),
    inference(equality_resolution,[],[f5102])).

fof(f5102,plain,
    ( ! [X0,X1] :
        ( k4_tarski(X0,X1) != k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0))))
        | sK2(k4_tarski(sK7(k8_filter_1(sK0),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK5(k8_filter_1(sK0),k1_relat_1(k8_filter_1(sK0)))),sK0) = X0 )
    | ~ spl15_142 ),
    inference(superposition,[],[f130,f1858])).

fof(f2016,plain,
    ( ~ spl15_11
    | spl15_7
    | ~ spl15_64 ),
    inference(avatar_split_clause,[],[f2011,f903,f194,f206])).

fof(f194,plain,
    ( spl15_7
  <=> u1_struct_0(sK0) != k3_relat_1(k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f903,plain,
    ( spl15_64
  <=> k1_relat_1(k8_filter_1(sK0)) = k3_relat_1(k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_64])])).

fof(f2011,plain,
    ( k1_relat_1(k8_filter_1(sK0)) != u1_struct_0(sK0)
    | ~ spl15_7
    | ~ spl15_64 ),
    inference(superposition,[],[f195,f904])).

fof(f904,plain,
    ( k1_relat_1(k8_filter_1(sK0)) = k3_relat_1(k8_filter_1(sK0))
    | ~ spl15_64 ),
    inference(avatar_component_clause,[],[f903])).

fof(f195,plain,
    ( u1_struct_0(sK0) != k3_relat_1(k8_filter_1(sK0))
    | ~ spl15_7 ),
    inference(avatar_component_clause,[],[f194])).

fof(f2010,plain,
    ( spl15_64
    | ~ spl15_20
    | ~ spl15_140 ),
    inference(avatar_split_clause,[],[f1970,f1851,f243,f903])).

fof(f1851,plain,
    ( spl15_140
  <=> k1_relat_1(k8_filter_1(sK0)) = k2_relat_1(k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_140])])).

fof(f1970,plain,
    ( k1_relat_1(k8_filter_1(sK0)) = k3_relat_1(k8_filter_1(sK0))
    | ~ spl15_20
    | ~ spl15_140 ),
    inference(forward_demodulation,[],[f1931,f101])).

fof(f1931,plain,
    ( k3_relat_1(k8_filter_1(sK0)) = k2_xboole_0(k1_relat_1(k8_filter_1(sK0)),k1_relat_1(k8_filter_1(sK0)))
    | ~ spl15_20
    | ~ spl15_140 ),
    inference(backward_demodulation,[],[f1852,f244])).

fof(f1852,plain,
    ( k1_relat_1(k8_filter_1(sK0)) = k2_relat_1(k8_filter_1(sK0))
    | ~ spl15_140 ),
    inference(avatar_component_clause,[],[f1851])).

fof(f315,plain,
    ( spl15_1
    | ~ spl15_14
    | ~ spl15_30 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_14
    | ~ spl15_30 ),
    inference(subsumption_resolution,[],[f313,f149])).

fof(f313,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_14
    | ~ spl15_30 ),
    inference(subsumption_resolution,[],[f309,f222])).

fof(f222,plain,
    ( l1_struct_0(sK0)
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl15_14
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f309,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_30 ),
    inference(resolution,[],[f304,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',fc2_struct_0)).

fof(f304,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl15_30 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl15_30
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_30])])).

fof(f308,plain,
    ( spl15_30
    | spl15_32
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f298,f162,f155,f148,f306,f303])).

fof(f298,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(X1,X2),k8_filter_1(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X2)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(X1,X2),k8_filter_1(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X2)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(superposition,[],[f188,f132])).

fof(f188,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7),k8_filter_1(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X6,X7) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(forward_demodulation,[],[f187,f177])).

fof(f187,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X6,X7)
        | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7),a_1_0_filter_1(sK0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f186,f149])).

fof(f186,plain,
    ( ! [X6,X7] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X6,X7)
        | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7),a_1_0_filter_1(sK0)) )
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f172,f156])).

fof(f172,plain,
    ( ! [X6,X7] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X6,X7)
        | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X6,X7),a_1_0_filter_1(sK0)) )
    | ~ spl15_4 ),
    inference(resolution,[],[f163,f138])).

fof(f138,plain,(
    ! [X2,X3,X1] :
      ( ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r3_lattices(X1,X2,X3)
      | r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),a_1_0_filter_1(X1)) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
      | ~ r3_lattices(X1,X2,X3)
      | r2_hidden(X0,a_1_0_filter_1(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f286,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | spl15_29 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_29 ),
    inference(subsumption_resolution,[],[f284,f163])).

fof(f284,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_29 ),
    inference(subsumption_resolution,[],[f283,f156])).

fof(f283,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl15_1
    | ~ spl15_29 ),
    inference(subsumption_resolution,[],[f282,f149])).

fof(f282,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl15_29 ),
    inference(resolution,[],[f266,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',cc1_lattices)).

fof(f266,plain,
    ( ~ v6_lattices(sK0)
    | ~ spl15_29 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl15_29
  <=> ~ v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_29])])).

fof(f279,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | spl15_27 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_27 ),
    inference(subsumption_resolution,[],[f277,f163])).

fof(f277,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_27 ),
    inference(subsumption_resolution,[],[f276,f156])).

fof(f276,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl15_1
    | ~ spl15_27 ),
    inference(subsumption_resolution,[],[f275,f149])).

fof(f275,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl15_27 ),
    inference(resolution,[],[f260,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f260,plain,
    ( ~ v8_lattices(sK0)
    | ~ spl15_27 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl15_27
  <=> ~ v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_27])])).

fof(f272,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | spl15_25 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_25 ),
    inference(subsumption_resolution,[],[f270,f163])).

fof(f270,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_25 ),
    inference(subsumption_resolution,[],[f269,f156])).

fof(f269,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl15_1
    | ~ spl15_25 ),
    inference(subsumption_resolution,[],[f268,f149])).

fof(f268,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl15_25 ),
    inference(resolution,[],[f254,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f254,plain,
    ( ~ v9_lattices(sK0)
    | ~ spl15_25 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl15_25
  <=> ~ v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_25])])).

fof(f267,plain,
    ( spl15_22
    | ~ spl15_25
    | ~ spl15_27
    | ~ spl15_29
    | spl15_1
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f189,f162,f148,f265,f259,f253,f247])).

fof(f189,plain,
    ( ! [X8] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r3_lattices(sK0,X8,X8) )
    | ~ spl15_1
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f173,f149])).

fof(f173,plain,
    ( ! [X8] :
        ( v2_struct_0(sK0)
        | ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r3_lattices(sK0,X8,X8) )
    | ~ spl15_4 ),
    inference(resolution,[],[f163,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ v6_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r3_lattices(X1,X0,X0) ) ),
    inference(condensation,[],[f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_lattices(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',reflexivity_r3_lattices)).

fof(f245,plain,
    ( spl15_20
    | ~ spl15_16 ),
    inference(avatar_split_clause,[],[f231,f228,f243])).

fof(f228,plain,
    ( spl15_16
  <=> v1_relat_1(k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f231,plain,
    ( k3_relat_1(k8_filter_1(sK0)) = k2_xboole_0(k1_relat_1(k8_filter_1(sK0)),k2_relat_1(k8_filter_1(sK0)))
    | ~ spl15_16 ),
    inference(resolution,[],[f229,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',d6_relat_1)).

fof(f229,plain,
    ( v1_relat_1(k8_filter_1(sK0))
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f228])).

fof(f238,plain,
    ( spl15_18
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f177,f162,f155,f148,f236])).

fof(f230,plain,
    ( spl15_16
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f175,f162,f155,f148,f228])).

fof(f175,plain,
    ( v1_relat_1(k8_filter_1(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f174,f149])).

fof(f174,plain,
    ( v2_struct_0(sK0)
    | v1_relat_1(k8_filter_1(sK0))
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f166,f156])).

fof(f166,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v1_relat_1(k8_filter_1(sK0))
    | ~ spl15_4 ),
    inference(resolution,[],[f163,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | v1_relat_1(k8_filter_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => v1_relat_1(k8_filter_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',dt_k8_filter_1)).

fof(f223,plain,
    ( spl15_14
    | ~ spl15_12 ),
    inference(avatar_split_clause,[],[f216,f213,f221])).

fof(f213,plain,
    ( spl15_12
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).

fof(f216,plain,
    ( l1_struct_0(sK0)
    | ~ spl15_12 ),
    inference(resolution,[],[f214,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ l2_lattices(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',dt_l2_lattices)).

fof(f214,plain,
    ( l2_lattices(sK0)
    | ~ spl15_12 ),
    inference(avatar_component_clause,[],[f213])).

fof(f215,plain,
    ( spl15_12
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f165,f162,f213])).

fof(f165,plain,
    ( l2_lattices(sK0)
    | ~ spl15_4 ),
    inference(resolution,[],[f163,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t33_filter_1.p',dt_l3_lattices)).

fof(f208,plain,
    ( ~ spl15_7
    | ~ spl15_9
    | ~ spl15_11 ),
    inference(avatar_split_clause,[],[f79,f206,f200,f194])).

fof(f164,plain,(
    spl15_4 ),
    inference(avatar_split_clause,[],[f82,f162])).

fof(f82,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f157,plain,(
    spl15_2 ),
    inference(avatar_split_clause,[],[f81,f155])).

fof(f81,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f150,plain,(
    ~ spl15_1 ),
    inference(avatar_split_clause,[],[f80,f148])).

fof(f80,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
