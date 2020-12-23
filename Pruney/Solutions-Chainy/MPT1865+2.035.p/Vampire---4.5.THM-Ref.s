%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:05 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 145 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  225 ( 716 expanded)
%              Number of equality atoms :   10 (  69 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f111,f132,f134,f136])).

fof(f136,plain,
    ( ~ spl7_1
    | spl7_6 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl7_1
    | spl7_6 ),
    inference(subsumption_resolution,[],[f131,f112])).

fof(f112,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_1 ),
    inference(resolution,[],[f104,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f104,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl7_1
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f131,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_6
  <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f134,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f127,f98])).

fof(f98,plain,(
    r1_tarski(k1_tarski(sK2),sK1) ),
    inference(resolution,[],[f54,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f54,plain,(
    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f20,f32])).

fof(f20,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

fof(f127,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_5
  <=> r1_tarski(k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f132,plain,
    ( ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f91,f129,f125])).

fof(f91,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(sK2),sK1) ),
    inference(subsumption_resolution,[],[f90,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f59,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f56,f23])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

fof(f22,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f90,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(sK2),sK1) ),
    inference(subsumption_resolution,[],[f89,f62])).

fof(f62,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,sK1)
      | v4_pre_topc(sK4(sK0,sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f61,f21])).

fof(f61,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,sK1)
      | v4_pre_topc(sK4(sK0,sK1,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f57,f23])).

fof(f57,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,sK1)
      | v4_pre_topc(sK4(sK0,sK1,X1),sK0) ) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | v4_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f89,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(sK2),sK1) ),
    inference(subsumption_resolution,[],[f88,f22])).

fof(f88,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(sK2),sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f87,f21])).

fof(f87,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(sK2),sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f84,f23])).

fof(f84,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tarski(sK2),sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f42,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | sQ6_eqProxy(k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)),X2)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(equality_proxy_replacement,[],[f28,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X3] :
      ( ~ sQ6_eqProxy(k9_subset_1(u1_struct_0(sK0),sK1,X3),k1_tarski(sK2))
      | ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(equality_proxy_replacement,[],[f18,f39])).

fof(f18,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f111,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f108,f83])).

fof(f83,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f77,f55])).

fof(f55,plain,(
    ~ sP5(sK1) ),
    inference(resolution,[],[f20,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f36,f37_D])).

fof(f37,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f37_D])).

fof(f37_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f77,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | sP5(sK1) ),
    inference(resolution,[],[f21,f37])).

fof(f108,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f109,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f65,f106,f102])).

fof(f65,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f19,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f19,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n024.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 20:52:06 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.12/0.34  % (32281)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.12/0.35  % (32281)Refutation not found, incomplete strategy% (32281)------------------------------
% 0.12/0.35  % (32281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.36  % (32281)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.36  
% 0.12/0.36  % (32281)Memory used [KB]: 10746
% 0.12/0.36  % (32281)Time elapsed: 0.049 s
% 0.12/0.36  % (32281)------------------------------
% 0.12/0.36  % (32281)------------------------------
% 0.12/0.36  % (32282)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.12/0.36  % (32287)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.12/0.36  % (32283)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.12/0.36  % (32292)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.12/0.36  % (32292)Refutation found. Thanks to Tanya!
% 0.12/0.36  % SZS status Theorem for theBenchmark
% 0.12/0.36  % SZS output start Proof for theBenchmark
% 0.12/0.36  fof(f137,plain,(
% 0.12/0.36    $false),
% 0.12/0.36    inference(avatar_sat_refutation,[],[f109,f111,f132,f134,f136])).
% 0.12/0.36  fof(f136,plain,(
% 0.12/0.36    ~spl7_1 | spl7_6),
% 0.12/0.36    inference(avatar_contradiction_clause,[],[f135])).
% 0.12/0.36  fof(f135,plain,(
% 0.12/0.36    $false | (~spl7_1 | spl7_6)),
% 0.12/0.36    inference(subsumption_resolution,[],[f131,f112])).
% 0.12/0.36  fof(f112,plain,(
% 0.12/0.36    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_1),
% 0.12/0.36    inference(resolution,[],[f104,f32])).
% 0.12/0.36  fof(f32,plain,(
% 0.12/0.36    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.12/0.36    inference(cnf_transformation,[],[f14])).
% 0.12/0.36  fof(f14,plain,(
% 0.12/0.36    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.12/0.36    inference(ennf_transformation,[],[f3])).
% 0.12/0.36  fof(f3,axiom,(
% 0.12/0.36    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.12/0.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.12/0.36  fof(f104,plain,(
% 0.12/0.36    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl7_1),
% 0.12/0.36    inference(avatar_component_clause,[],[f102])).
% 0.12/0.36  fof(f102,plain,(
% 0.12/0.36    spl7_1 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 0.12/0.36    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.12/0.36  fof(f131,plain,(
% 0.12/0.36    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl7_6),
% 0.12/0.36    inference(avatar_component_clause,[],[f129])).
% 0.12/0.36  fof(f129,plain,(
% 0.12/0.36    spl7_6 <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.12/0.36    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.12/0.36  fof(f134,plain,(
% 0.12/0.36    spl7_5),
% 0.12/0.36    inference(avatar_contradiction_clause,[],[f133])).
% 0.12/0.36  fof(f133,plain,(
% 0.12/0.36    $false | spl7_5),
% 0.12/0.36    inference(subsumption_resolution,[],[f127,f98])).
% 0.12/0.36  fof(f98,plain,(
% 0.12/0.36    r1_tarski(k1_tarski(sK2),sK1)),
% 0.12/0.36    inference(resolution,[],[f54,f35])).
% 0.12/0.36  fof(f35,plain,(
% 0.12/0.36    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.12/0.36    inference(cnf_transformation,[],[f5])).
% 0.12/0.36  fof(f5,axiom,(
% 0.12/0.36    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.12/0.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.12/0.36  fof(f54,plain,(
% 0.12/0.36    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1))),
% 0.12/0.36    inference(resolution,[],[f20,f32])).
% 0.12/0.36  fof(f20,plain,(
% 0.12/0.36    r2_hidden(sK2,sK1)),
% 0.12/0.36    inference(cnf_transformation,[],[f11])).
% 0.12/0.36  fof(f11,plain,(
% 0.12/0.36    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.12/0.36    inference(flattening,[],[f10])).
% 0.12/0.36  fof(f10,plain,(
% 0.12/0.36    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.12/0.36    inference(ennf_transformation,[],[f9])).
% 0.12/0.36  fof(f9,negated_conjecture,(
% 0.12/0.36    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.12/0.36    inference(negated_conjecture,[],[f8])).
% 0.12/0.36  fof(f8,conjecture,(
% 0.12/0.36    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.12/0.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).
% 0.12/0.36  fof(f127,plain,(
% 0.12/0.36    ~r1_tarski(k1_tarski(sK2),sK1) | spl7_5),
% 0.12/0.36    inference(avatar_component_clause,[],[f125])).
% 0.12/0.36  fof(f125,plain,(
% 0.12/0.36    spl7_5 <=> r1_tarski(k1_tarski(sK2),sK1)),
% 0.12/0.36    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.12/0.36  fof(f132,plain,(
% 0.12/0.36    ~spl7_5 | ~spl7_6),
% 0.12/0.36    inference(avatar_split_clause,[],[f91,f129,f125])).
% 0.12/0.36  fof(f91,plain,(
% 0.12/0.36    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tarski(sK2),sK1)),
% 0.12/0.36    inference(subsumption_resolution,[],[f90,f60])).
% 0.12/0.36  fof(f60,plain,(
% 0.12/0.36    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.12/0.36    inference(subsumption_resolution,[],[f59,f21])).
% 0.12/0.36  fof(f21,plain,(
% 0.12/0.36    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.12/0.36    inference(cnf_transformation,[],[f11])).
% 0.12/0.36  fof(f59,plain,(
% 0.12/0.36    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.12/0.36    inference(subsumption_resolution,[],[f56,f23])).
% 0.12/0.36  fof(f23,plain,(
% 0.12/0.36    l1_pre_topc(sK0)),
% 0.12/0.36    inference(cnf_transformation,[],[f11])).
% 0.12/0.36  fof(f56,plain,(
% 0.12/0.36    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.12/0.36    inference(resolution,[],[f22,f26])).
% 0.12/0.36  fof(f26,plain,(
% 0.12/0.36    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0)) )),
% 0.12/0.36    inference(cnf_transformation,[],[f13])).
% 0.12/0.36  fof(f13,plain,(
% 0.12/0.36    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.12/0.36    inference(flattening,[],[f12])).
% 0.12/0.36  fof(f12,plain,(
% 0.12/0.36    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.12/0.36    inference(ennf_transformation,[],[f7])).
% 0.12/0.36  fof(f7,axiom,(
% 0.12/0.36    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.12/0.36    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 0.12/0.36  fof(f22,plain,(
% 0.12/0.36    v2_tex_2(sK1,sK0)),
% 0.12/0.36    inference(cnf_transformation,[],[f11])).
% 0.12/0.36  fof(f90,plain,(
% 0.12/0.36    ~m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tarski(sK2),sK1)),
% 0.12/0.36    inference(subsumption_resolution,[],[f89,f62])).
% 0.12/0.36  fof(f62,plain,(
% 0.12/0.36    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK1) | v4_pre_topc(sK4(sK0,sK1,X1),sK0)) )),
% 0.12/0.36    inference(subsumption_resolution,[],[f61,f21])).
% 0.12/0.36  fof(f61,plain,(
% 0.12/0.36    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK1) | v4_pre_topc(sK4(sK0,sK1,X1),sK0)) )),
% 0.12/0.36    inference(subsumption_resolution,[],[f57,f23])).
% 0.12/0.36  fof(f57,plain,(
% 0.12/0.36    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK1) | v4_pre_topc(sK4(sK0,sK1,X1),sK0)) )),
% 0.12/0.36    inference(resolution,[],[f22,f27])).
% 0.12/0.36  fof(f27,plain,(
% 0.12/0.36    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | v4_pre_topc(sK4(X0,X1,X2),X0) | ~v2_tex_2(X1,X0)) )),
% 0.12/0.36    inference(cnf_transformation,[],[f13])).
% 0.12/0.36  fof(f89,plain,(
% 0.12/0.36    ~v4_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0) | ~m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tarski(sK2),sK1)),
% 0.12/0.36    inference(subsumption_resolution,[],[f88,f22])).
% 0.12/0.36  fof(f88,plain,(
% 0.12/0.36    ~v4_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0) | ~m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tarski(sK2),sK1) | ~v2_tex_2(sK1,sK0)),
% 0.12/0.36    inference(subsumption_resolution,[],[f87,f21])).
% 0.12/0.36  fof(f87,plain,(
% 0.12/0.36    ~v4_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0) | ~m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tarski(sK2),sK1) | ~v2_tex_2(sK1,sK0)),
% 0.12/0.36    inference(subsumption_resolution,[],[f84,f23])).
% 0.12/0.37  fof(f84,plain,(
% 0.12/0.37    ~v4_pre_topc(sK4(sK0,sK1,k1_tarski(sK2)),sK0) | ~m1_subset_1(sK4(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tarski(sK2),sK1) | ~v2_tex_2(sK1,sK0)),
% 0.12/0.37    inference(resolution,[],[f42,f43])).
% 0.12/0.37  fof(f43,plain,(
% 0.12/0.37    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | sQ6_eqProxy(k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)),X2) | ~v2_tex_2(X1,X0)) )),
% 0.12/0.37    inference(equality_proxy_replacement,[],[f28,f39])).
% 0.12/0.37  fof(f39,plain,(
% 0.12/0.37    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.12/0.37    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.12/0.37  fof(f28,plain,(
% 0.12/0.37    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2 | ~v2_tex_2(X1,X0)) )),
% 0.12/0.37    inference(cnf_transformation,[],[f13])).
% 0.12/0.37  fof(f42,plain,(
% 0.12/0.37    ( ! [X3] : (~sQ6_eqProxy(k9_subset_1(u1_struct_0(sK0),sK1,X3),k1_tarski(sK2)) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.12/0.37    inference(equality_proxy_replacement,[],[f18,f39])).
% 0.12/0.37  fof(f18,plain,(
% 0.12/0.37    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X3,sK0) | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)) )),
% 0.12/0.37    inference(cnf_transformation,[],[f11])).
% 0.12/0.37  fof(f111,plain,(
% 0.12/0.37    ~spl7_2),
% 0.12/0.37    inference(avatar_contradiction_clause,[],[f110])).
% 0.12/0.37  fof(f110,plain,(
% 0.12/0.37    $false | ~spl7_2),
% 0.12/0.37    inference(subsumption_resolution,[],[f108,f83])).
% 0.12/0.37  fof(f83,plain,(
% 0.12/0.37    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.12/0.37    inference(subsumption_resolution,[],[f77,f55])).
% 0.12/0.37  fof(f55,plain,(
% 0.12/0.37    ~sP5(sK1)),
% 0.12/0.37    inference(resolution,[],[f20,f38])).
% 0.12/0.37  fof(f38,plain,(
% 0.12/0.37    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP5(X1)) )),
% 0.12/0.37    inference(general_splitting,[],[f36,f37_D])).
% 0.12/0.37  fof(f37,plain,(
% 0.12/0.37    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP5(X1)) )),
% 0.12/0.37    inference(cnf_transformation,[],[f37_D])).
% 0.12/0.37  fof(f37_D,plain,(
% 0.12/0.37    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP5(X1)) )),
% 0.12/0.37    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.12/0.37  fof(f36,plain,(
% 0.12/0.37    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.12/0.37    inference(cnf_transformation,[],[f17])).
% 0.12/0.37  fof(f17,plain,(
% 0.12/0.37    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.12/0.37    inference(ennf_transformation,[],[f6])).
% 0.12/0.37  fof(f6,axiom,(
% 0.12/0.37    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.12/0.37  fof(f77,plain,(
% 0.12/0.37    ~v1_xboole_0(u1_struct_0(sK0)) | sP5(sK1)),
% 0.12/0.37    inference(resolution,[],[f21,f37])).
% 0.12/0.37  fof(f108,plain,(
% 0.12/0.37    v1_xboole_0(u1_struct_0(sK0)) | ~spl7_2),
% 0.12/0.37    inference(avatar_component_clause,[],[f106])).
% 0.12/0.37  fof(f106,plain,(
% 0.12/0.37    spl7_2 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.12/0.37    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.12/0.37  fof(f109,plain,(
% 0.12/0.37    spl7_1 | spl7_2),
% 0.12/0.37    inference(avatar_split_clause,[],[f65,f106,f102])).
% 0.12/0.37  fof(f65,plain,(
% 0.12/0.37    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK2,u1_struct_0(sK0))),
% 0.12/0.37    inference(resolution,[],[f19,f33])).
% 0.12/0.37  fof(f33,plain,(
% 0.12/0.37    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.12/0.37    inference(cnf_transformation,[],[f16])).
% 0.12/0.37  fof(f16,plain,(
% 0.12/0.37    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.12/0.37    inference(flattening,[],[f15])).
% 0.12/0.37  fof(f15,plain,(
% 0.12/0.37    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.12/0.37    inference(ennf_transformation,[],[f4])).
% 0.12/0.37  fof(f4,axiom,(
% 0.12/0.37    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.12/0.37  fof(f19,plain,(
% 0.12/0.37    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.12/0.37    inference(cnf_transformation,[],[f11])).
% 0.12/0.37  % SZS output end Proof for theBenchmark
% 0.12/0.37  % (32292)------------------------------
% 0.12/0.37  % (32292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.37  % (32292)Termination reason: Refutation
% 0.12/0.37  
% 0.12/0.37  % (32292)Memory used [KB]: 6268
% 0.12/0.37  % (32284)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.12/0.37  % (32292)Time elapsed: 0.060 s
% 0.12/0.37  % (32292)------------------------------
% 0.12/0.37  % (32292)------------------------------
% 0.12/0.37  % (32278)Success in time 0.093 s
%------------------------------------------------------------------------------
