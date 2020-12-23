%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t57_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:45 EDT 2019

% Result     : Theorem 6.98s
% Output     : Refutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 638 expanded)
%              Number of leaves         :   24 ( 168 expanded)
%              Depth                    :   13
%              Number of atoms          :  298 (1538 expanded)
%              Number of equality atoms :   42 ( 142 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14521,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f1456,f1804,f1883,f4108,f4460,f9181,f13967,f13974,f14322,f14430])).

fof(f14430,plain,
    ( ~ spl6_0
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f14336])).

fof(f14336,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f3824,f14331])).

fof(f14331,plain,
    ( u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) != k1_toler_1(u1_orders_2(sK0),sK1)
    | ~ spl6_0
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f14329,f3825])).

fof(f3825,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = X0 ),
    inference(unit_resulting_resolution,[],[f441,f430])).

fof(f430,plain,(
    ! [X2,X3,X1] :
      ( g1_orders_2(X2,X3) != g1_orders_2(X1,k1_toler_1(u1_orders_2(sK0),X1))
      | X1 = X2 ) ),
    inference(resolution,[],[f168,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',free_g1_orders_2)).

fof(f168,plain,(
    ! [X0] : m1_subset_1(k1_toler_1(u1_orders_2(sK0),X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(unit_resulting_resolution,[],[f158,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',dt_k1_toler_1)).

fof(f158,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f83,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',cc1_relset_1)).

fof(f83,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f50,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',dt_u1_orders_2)).

fof(f50,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
            | ~ v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
              & v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( m1_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0)
            & v4_yellow_0(g1_orders_2(X1,k1_toler_1(u1_orders_2(X0),X1)),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',t57_yellow_0)).

fof(f441,plain,(
    ! [X0] : g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))),u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0)))) ),
    inference(unit_resulting_resolution,[],[f425,f426,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',abstractness_v1_orders_2)).

fof(f426,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) ),
    inference(unit_resulting_resolution,[],[f168,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | l1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',dt_g1_orders_2)).

fof(f425,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) ),
    inference(unit_resulting_resolution,[],[f168,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14329,plain,
    ( u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) != k1_toler_1(u1_orders_2(sK0),u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))))
    | ~ spl6_0
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f50,f118,f109,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v4_yellow_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',d14_yellow_0)).

fof(f109,plain,
    ( m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_0
  <=> m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f118,plain,
    ( ~ v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_3
  <=> ~ v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f3824,plain,(
    ! [X0] : u1_orders_2(g1_orders_2(X0,k1_toler_1(u1_orders_2(sK0),X0))) = k1_toler_1(u1_orders_2(sK0),X0) ),
    inference(unit_resulting_resolution,[],[f441,f431])).

fof(f431,plain,(
    ! [X6,X4,X5] :
      ( g1_orders_2(X5,X6) != g1_orders_2(X4,k1_toler_1(u1_orders_2(sK0),X4))
      | k1_toler_1(u1_orders_2(sK0),X4) = X6 ) ),
    inference(resolution,[],[f168,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14322,plain,(
    spl6_119 ),
    inference(avatar_contradiction_clause,[],[f13977])).

fof(f13977,plain,
    ( $false
    | ~ spl6_119 ),
    inference(unit_resulting_resolution,[],[f168,f4101,f64])).

fof(f4101,plain,
    ( ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | ~ spl6_119 ),
    inference(avatar_component_clause,[],[f4100])).

fof(f4100,plain,
    ( spl6_119
  <=> ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).

fof(f13974,plain,(
    spl6_247 ),
    inference(avatar_contradiction_clause,[],[f13970])).

fof(f13970,plain,
    ( $false
    | ~ spl6_247 ),
    inference(unit_resulting_resolution,[],[f513,f13966,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',t3_subset)).

fof(f13966,plain,
    ( ~ r1_tarski(k1_toler_1(u1_orders_2(sK0),sK1),u1_orders_2(sK0))
    | ~ spl6_247 ),
    inference(avatar_component_clause,[],[f13965])).

fof(f13965,plain,
    ( spl6_247
  <=> ~ r1_tarski(k1_toler_1(u1_orders_2(sK0),sK1),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_247])])).

fof(f513,plain,(
    ! [X0] : m1_subset_1(k1_toler_1(u1_orders_2(sK0),X0),k1_zfmisc_1(u1_orders_2(sK0))) ),
    inference(unit_resulting_resolution,[],[f512,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f512,plain,(
    ! [X0] : r1_tarski(k1_toler_1(u1_orders_2(sK0),X0),u1_orders_2(sK0)) ),
    inference(superposition,[],[f76,f173])).

fof(f173,plain,(
    ! [X0] : k1_toler_1(u1_orders_2(sK0),X0) = k3_xboole_0(u1_orders_2(sK0),k2_zfmisc_1(X0,X0)) ),
    inference(forward_demodulation,[],[f166,f167])).

fof(f167,plain,(
    ! [X0] : k1_toler_1(u1_orders_2(sK0),X0) = k2_wellord1(u1_orders_2(sK0),X0) ),
    inference(unit_resulting_resolution,[],[f158,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_toler_1(X0,X1) = k2_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_toler_1(X0,X1) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => k1_toler_1(X0,X1) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',redefinition_k1_toler_1)).

fof(f166,plain,(
    ! [X0] : k3_xboole_0(u1_orders_2(sK0),k2_zfmisc_1(X0,X0)) = k2_wellord1(u1_orders_2(sK0),X0) ),
    inference(unit_resulting_resolution,[],[f158,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',d6_wellord1)).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',t17_xboole_1)).

fof(f13967,plain,
    ( ~ spl6_119
    | ~ spl6_121
    | ~ spl6_247
    | spl6_117
    | ~ spl6_128 ),
    inference(avatar_split_clause,[],[f4510,f4458,f4094,f13965,f4106,f4100])).

fof(f4106,plain,
    ( spl6_121
  <=> ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f4094,plain,
    ( spl6_117
  <=> ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f4458,plain,
    ( spl6_128
  <=> ! [X2] :
        ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(sK0))
        | m1_yellow_0(X2,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X2)
        | ~ r1_tarski(u1_orders_2(X2),u1_orders_2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).

fof(f4510,plain,
    ( ~ r1_tarski(k1_toler_1(u1_orders_2(sK0),sK1),u1_orders_2(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | ~ spl6_117
    | ~ spl6_128 ),
    inference(forward_demodulation,[],[f4509,f3824])).

fof(f4509,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | ~ r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0))
    | ~ spl6_117
    | ~ spl6_128 ),
    inference(forward_demodulation,[],[f4502,f3825])).

fof(f4502,plain,
    ( ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | ~ r1_tarski(u1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_orders_2(sK0))
    | ~ spl6_117
    | ~ spl6_128 ),
    inference(resolution,[],[f4459,f4095])).

fof(f4095,plain,
    ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl6_117 ),
    inference(avatar_component_clause,[],[f4094])).

fof(f4459,plain,
    ( ! [X2] :
        ( m1_yellow_0(X2,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(sK0))
        | ~ l1_orders_2(X2)
        | ~ r1_tarski(u1_orders_2(X2),u1_orders_2(sK0)) )
    | ~ spl6_128 ),
    inference(avatar_component_clause,[],[f4458])).

fof(f9181,plain,(
    spl6_121 ),
    inference(avatar_contradiction_clause,[],[f9177])).

fof(f9177,plain,
    ( $false
    | ~ spl6_121 ),
    inference(unit_resulting_resolution,[],[f49,f4107,f75])).

fof(f4107,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl6_121 ),
    inference(avatar_component_clause,[],[f4106])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f4460,plain,
    ( ~ spl6_37
    | spl6_128 ),
    inference(avatar_split_clause,[],[f1072,f4458,f1386])).

fof(f1386,plain,
    ( spl6_37
  <=> ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f1072,plain,(
    ! [X2] :
      ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(sK0))
      | ~ r1_tarski(u1_orders_2(X2),u1_orders_2(sK0))
      | ~ l1_orders_2(X2)
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
      | m1_yellow_0(X2,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ) ),
    inference(forward_demodulation,[],[f1066,f1048])).

fof(f1048,plain,(
    u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(unit_resulting_resolution,[],[f218,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f83,f61])).

fof(f218,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    inference(unit_resulting_resolution,[],[f156,f157,f65])).

fof(f157,plain,(
    l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(unit_resulting_resolution,[],[f83,f64])).

fof(f156,plain,(
    v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(unit_resulting_resolution,[],[f83,f63])).

fof(f1066,plain,(
    ! [X2] :
      ( ~ r1_tarski(u1_orders_2(X2),u1_orders_2(sK0))
      | ~ l1_orders_2(X2)
      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
      | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
      | m1_yellow_0(X2,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ) ),
    inference(superposition,[],[f60,f1047])).

fof(f1047,plain,(
    u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(unit_resulting_resolution,[],[f218,f162])).

fof(f162,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_orders_2(sK0) = X3 ) ),
    inference(resolution,[],[f83,f62])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ l1_orders_2(X1)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_yellow_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t57_yellow_0.p',d13_yellow_0)).

fof(f4108,plain,
    ( ~ spl6_117
    | ~ spl6_119
    | ~ spl6_121
    | spl6_1
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f3844,f1802,f111,f4106,f4100,f4094])).

fof(f111,plain,
    ( spl6_1
  <=> ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1802,plain,
    ( spl6_50
  <=> ! [X0] :
        ( ~ l1_orders_2(X0)
        | m1_yellow_0(X0,sK0)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_yellow_0(X0,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f3844,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl6_1
    | ~ spl6_50 ),
    inference(backward_demodulation,[],[f3825,f1902])).

fof(f1902,plain,
    ( ~ l1_orders_2(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)))
    | ~ r1_tarski(u1_struct_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1))),u1_struct_0(sK0))
    | ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl6_1
    | ~ spl6_50 ),
    inference(resolution,[],[f1803,f112])).

fof(f112,plain,
    ( ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f1803,plain,
    ( ! [X0] :
        ( m1_yellow_0(X0,sK0)
        | ~ l1_orders_2(X0)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_yellow_0(X0,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f1802])).

fof(f1883,plain,(
    spl6_49 ),
    inference(avatar_contradiction_clause,[],[f1805])).

fof(f1805,plain,
    ( $false
    | ~ spl6_49 ),
    inference(unit_resulting_resolution,[],[f50,f1800])).

fof(f1800,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f1799])).

fof(f1799,plain,
    ( spl6_49
  <=> ~ l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f1804,plain,
    ( ~ spl6_49
    | spl6_50 ),
    inference(avatar_split_clause,[],[f1087,f1802,f1799])).

fof(f1087,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X0,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | m1_yellow_0(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f1084])).

fof(f1084,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X0,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
      | ~ l1_orders_2(X0)
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | m1_yellow_0(X0,sK0) ) ),
    inference(resolution,[],[f1058,f60])).

fof(f1058,plain,(
    ! [X0] :
      ( r1_tarski(u1_orders_2(X0),u1_orders_2(sK0))
      | ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X0,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ) ),
    inference(backward_demodulation,[],[f1047,f222])).

fof(f222,plain,(
    ! [X0] :
      ( r1_tarski(u1_orders_2(X0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
      | ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X0,g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ) ),
    inference(resolution,[],[f157,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1456,plain,(
    spl6_37 ),
    inference(avatar_contradiction_clause,[],[f1397])).

fof(f1397,plain,
    ( $false
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f83,f1387,f64])).

fof(f1387,plain,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f1386])).

fof(f119,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f48,f117,f111])).

fof(f48,plain,
    ( ~ v4_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0)
    | ~ m1_yellow_0(g1_orders_2(sK1,k1_toler_1(u1_orders_2(sK0),sK1)),sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
