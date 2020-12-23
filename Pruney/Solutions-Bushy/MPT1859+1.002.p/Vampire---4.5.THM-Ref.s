%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1859+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:46 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  182 (2324 expanded)
%              Number of leaves         :   25 ( 637 expanded)
%              Depth                    :   24
%              Number of atoms          :  670 (12332 expanded)
%              Number of equality atoms :   81 (2222 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2003,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f119,f433,f454,f456,f2002])).

fof(f2002,plain,
    ( ~ spl6_1
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f2001])).

fof(f2001,plain,
    ( $false
    | ~ spl6_1
    | spl6_8 ),
    inference(subsumption_resolution,[],[f2000,f1755])).

fof(f1755,plain,
    ( r1_tarski(sK5(k9_setfam_1(sK1),u1_pre_topc(sK0)),sK1)
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f813,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f88,f63])).

fof(f63,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f813,plain,
    ( m1_subset_1(sK5(k9_setfam_1(sK1),u1_pre_topc(sK0)),k9_setfam_1(sK1))
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f502,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f502,plain,
    ( r2_hidden(sK5(k9_setfam_1(sK1),u1_pre_topc(sK0)),k9_setfam_1(sK1))
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f478,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f478,plain,
    ( ~ r1_tarski(k9_setfam_1(sK1),u1_pre_topc(sK0))
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f453,f466,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f466,plain,(
    r1_tarski(u1_pre_topc(sK0),k9_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f149,f105])).

fof(f149,plain,(
    m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(sK1))) ),
    inference(subsumption_resolution,[],[f130,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ v1_tdlat_3(sK0)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_tdlat_3(sK0)
      | v2_tex_2(sK1,sK0) )
    & u1_struct_0(sK0) = sK1
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_tdlat_3(X0)
              | v2_tex_2(X1,X0) )
            & u1_struct_0(X0) = X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v1_tdlat_3(sK0)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_tdlat_3(sK0)
            | v2_tex_2(X1,sK0) )
          & u1_struct_0(sK0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( ~ v1_tdlat_3(sK0)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_tdlat_3(sK0)
          | v2_tex_2(X1,sK0) )
        & u1_struct_0(sK0) = X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v1_tdlat_3(sK0)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_tdlat_3(sK0)
        | v2_tex_2(sK1,sK0) )
      & u1_struct_0(sK0) = sK1
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tdlat_3(X0)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_tdlat_3(X0)
            | v2_tex_2(X1,X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tdlat_3(X0)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_tdlat_3(X0)
            | v2_tex_2(X1,X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( u1_struct_0(X0) = X1
             => ( v2_tex_2(X1,X0)
              <=> v1_tdlat_3(X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( u1_struct_0(X0) = X1
             => ( v2_tex_2(X1,X0)
              <=> v1_tdlat_3(X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

fof(f130,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f93,f60])).

fof(f60,plain,(
    u1_struct_0(sK0) = sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f64,f63,f63])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f453,plain,
    ( k9_setfam_1(sK1) != u1_pre_topc(sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl6_8
  <=> k9_setfam_1(sK1) = u1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f2000,plain,
    ( ~ r1_tarski(sK5(k9_setfam_1(sK1),u1_pre_topc(sK0)),sK1)
    | ~ spl6_1
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f503,f1896])).

fof(f1896,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_pre_topc(sK0))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl6_1 ),
    inference(superposition,[],[f1825,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1825,plain,
    ( ! [X0] : r2_hidden(k3_xboole_0(X0,sK1),u1_pre_topc(sK0))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f648,f1821])).

fof(f1821,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = sK3(sK0,sK1,k3_xboole_0(X0,sK1))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1798,f725])).

fof(f725,plain,
    ( ! [X1] : k3_xboole_0(X1,sK1) = k3_xboole_0(sK1,sK3(sK0,sK1,k3_xboole_0(X1,sK1)))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f722,f487])).

fof(f487,plain,
    ( ! [X0] : m1_subset_1(sK3(sK0,sK1,k3_xboole_0(X0,sK1)),k9_setfam_1(sK1))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f112,f120,f463,f470,f191])).

fof(f191,plain,(
    ! [X24,X23] :
      ( ~ r1_tarski(X24,X23)
      | m1_subset_1(sK3(sK0,X23,X24),k9_setfam_1(sK1))
      | ~ m1_subset_1(X24,k9_setfam_1(sK1))
      | ~ v2_tex_2(X23,sK0)
      | ~ m1_subset_1(X23,k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f144,f58])).

fof(f144,plain,(
    ! [X24,X23] :
      ( m1_subset_1(sK3(sK0,X23,X24),k9_setfam_1(sK1))
      | ~ r1_tarski(X24,X23)
      | ~ m1_subset_1(X24,k9_setfam_1(sK1))
      | ~ v2_tex_2(X23,sK0)
      | ~ m1_subset_1(X23,k9_setfam_1(sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f99,f60])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X4),k9_setfam_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k9_setfam_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f68,f63,f63,f63])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
                    & v3_pre_topc(sK3(X0,X1,X4),X0)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f44,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v3_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
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
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f470,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f463,f105])).

fof(f463,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k9_setfam_1(sK1)) ),
    inference(backward_demodulation,[],[f461,f460])).

fof(f460,plain,(
    ! [X0] : k9_subset_1(sK1,X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(unit_resulting_resolution,[],[f120,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f91,f63])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f461,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(sK1,X0,sK1),k9_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f120,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f90,f63,f63])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f120,plain,(
    m1_subset_1(sK1,k9_setfam_1(sK1)) ),
    inference(forward_demodulation,[],[f92,f60])).

fof(f92,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f112,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f722,plain,
    ( ! [X1] :
        ( k3_xboole_0(X1,sK1) = k3_xboole_0(sK1,sK3(sK0,sK1,k3_xboole_0(X1,sK1)))
        | ~ m1_subset_1(sK3(sK0,sK1,k3_xboole_0(X1,sK1)),k9_setfam_1(sK1)) )
    | ~ spl6_1 ),
    inference(superposition,[],[f485,f107])).

fof(f485,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(sK1,sK1,sK3(sK0,sK1,k3_xboole_0(X0,sK1)))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f112,f120,f463,f470,f174])).

fof(f174,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(X13,X14)
      | k9_subset_1(sK1,X14,sK3(sK0,X14,X13)) = X13
      | ~ m1_subset_1(X13,k9_setfam_1(sK1))
      | ~ v2_tex_2(X14,sK0)
      | ~ m1_subset_1(X14,k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f139,f58])).

fof(f139,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k9_setfam_1(sK1))
      | k9_subset_1(sK1,X14,sK3(sK0,X14,X13)) = X13
      | ~ r1_tarski(X13,X14)
      | ~ v2_tex_2(X14,sK0)
      | ~ m1_subset_1(X14,k9_setfam_1(sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f97,f60])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k9_setfam_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f70,f63,f63])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1798,plain,
    ( ! [X0] : sK3(sK0,sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,sK3(sK0,sK1,k3_xboole_0(X0,sK1)))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f651,f982])).

fof(f982,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k3_xboole_0(sK1,X0) = X0 ) ),
    inference(superposition,[],[f633,f81])).

fof(f633,plain,(
    ! [X2] : k3_xboole_0(X2,sK1) = k3_xboole_0(sK1,k3_xboole_0(X2,sK1)) ),
    inference(superposition,[],[f483,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f483,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k3_xboole_0(k3_xboole_0(X0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f470,f81])).

fof(f651,plain,
    ( ! [X0] : r1_tarski(sK3(sK0,sK1,k3_xboole_0(X0,sK1)),sK1)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f487,f105])).

fof(f648,plain,
    ( ! [X0] : r2_hidden(sK3(sK0,sK1,k3_xboole_0(X0,sK1)),u1_pre_topc(sK0))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f486,f487,f198])).

fof(f198,plain,(
    ! [X26] :
      ( ~ v3_pre_topc(X26,sK0)
      | r2_hidden(X26,u1_pre_topc(sK0))
      | ~ m1_subset_1(X26,k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f146,f58])).

fof(f146,plain,(
    ! [X26] :
      ( ~ m1_subset_1(X26,k9_setfam_1(sK1))
      | r2_hidden(X26,u1_pre_topc(sK0))
      | ~ v3_pre_topc(X26,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f101,f60])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f74,f63])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f486,plain,
    ( ! [X0] : v3_pre_topc(sK3(sK0,sK1,k3_xboole_0(X0,sK1)),sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f112,f120,f463,f470,f180])).

fof(f180,plain,(
    ! [X17,X18] :
      ( v3_pre_topc(sK3(sK0,X18,X17),sK0)
      | ~ m1_subset_1(X17,k9_setfam_1(sK1))
      | ~ r1_tarski(X17,X18)
      | ~ v2_tex_2(X18,sK0)
      | ~ m1_subset_1(X18,k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f141,f58])).

fof(f141,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,k9_setfam_1(sK1))
      | v3_pre_topc(sK3(sK0,X18,X17),sK0)
      | ~ r1_tarski(X17,X18)
      | ~ v2_tex_2(X18,sK0)
      | ~ m1_subset_1(X18,k9_setfam_1(sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f98,f60])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK3(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k9_setfam_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f69,f63,f63])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK3(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f503,plain,
    ( ~ r2_hidden(sK5(k9_setfam_1(sK1),u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f478,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f456,plain,
    ( ~ spl6_2
    | spl6_8 ),
    inference(avatar_split_clause,[],[f455,f451,f115])).

fof(f115,plain,
    ( spl6_2
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f455,plain,
    ( k9_setfam_1(sK1) = u1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f128,f58])).

fof(f128,plain,
    ( k9_setfam_1(sK1) = u1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f66,f60])).

fof(f66,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(f454,plain,
    ( spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f449,f451,f115])).

fof(f449,plain,
    ( k9_setfam_1(sK1) != u1_pre_topc(sK0)
    | v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f129,f58])).

fof(f129,plain,
    ( k9_setfam_1(sK1) != u1_pre_topc(sK0)
    | v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f67,f60])).

fof(f67,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f433,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f431,f216])).

fof(f216,plain,
    ( m1_subset_1(sK2(sK0,sK1),u1_pre_topc(sK0))
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f113,f127,f164])).

fof(f164,plain,
    ( ! [X7] :
        ( v2_tex_2(X7,sK0)
        | ~ m1_subset_1(X7,u1_pre_topc(sK0))
        | m1_subset_1(sK2(sK0,X7),u1_pre_topc(sK0)) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f163,f125])).

fof(f125,plain,
    ( k9_setfam_1(sK1) = u1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f123,f60])).

fof(f123,plain,
    ( k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f58,f116,f66])).

fof(f116,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f163,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,u1_pre_topc(sK0))
        | v2_tex_2(X7,sK0)
        | m1_subset_1(sK2(sK0,X7),k9_setfam_1(sK1)) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f162,f125])).

fof(f162,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k9_setfam_1(sK1))
      | v2_tex_2(X7,sK0)
      | m1_subset_1(sK2(sK0,X7),k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f135,f58])).

fof(f135,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k9_setfam_1(sK1))
      | v2_tex_2(X7,sK0)
      | m1_subset_1(sK2(sK0,X7),k9_setfam_1(sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f96,f60])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f71,f63,f63])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f127,plain,
    ( m1_subset_1(sK1,u1_pre_topc(sK0))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f120,f125])).

fof(f113,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f431,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_pre_topc(sK0))
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f424,f282])).

fof(f282,plain,
    ( sK2(sK0,sK1) = k3_xboole_0(sK1,sK2(sK0,sK1))
    | spl6_1
    | ~ spl6_2 ),
    inference(superposition,[],[f218,f79])).

fof(f218,plain,
    ( sK2(sK0,sK1) = k3_xboole_0(sK2(sK0,sK1),sK1)
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f215,f81])).

fof(f215,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f113,f127,f161])).

fof(f161,plain,
    ( ! [X6] :
        ( v2_tex_2(X6,sK0)
        | ~ m1_subset_1(X6,u1_pre_topc(sK0))
        | r1_tarski(sK2(sK0,X6),X6) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f160,f125])).

fof(f160,plain,(
    ! [X6] :
      ( v2_tex_2(X6,sK0)
      | ~ m1_subset_1(X6,k9_setfam_1(sK1))
      | r1_tarski(sK2(sK0,X6),X6) ) ),
    inference(subsumption_resolution,[],[f134,f58])).

fof(f134,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k9_setfam_1(sK1))
      | v2_tex_2(X6,sK0)
      | r1_tarski(sK2(sK0,X6),X6)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f95,f60])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f72,f63])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f424,plain,
    ( sK2(sK0,sK1) != k3_xboole_0(sK1,sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_pre_topc(sK0))
    | spl6_1
    | ~ spl6_2 ),
    inference(superposition,[],[f250,f204])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X1,X0) = k9_subset_1(sK1,X1,X0)
        | ~ m1_subset_1(X0,u1_pre_topc(sK0)) )
    | ~ spl6_2 ),
    inference(superposition,[],[f107,f125])).

fof(f250,plain,
    ( sK2(sK0,sK1) != k9_subset_1(sK1,sK1,sK2(sK0,sK1))
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f113,f127,f216,f225,f153])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X1,u1_pre_topc(sK0))
        | sK2(sK0,X0) != k9_subset_1(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_pre_topc(sK0))
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f152,f125])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_pre_topc(sK0))
        | sK2(sK0,X0) != k9_subset_1(sK1,X0,X1)
        | v2_tex_2(X0,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k9_setfam_1(sK1)) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f151,f125])).

fof(f151,plain,(
    ! [X0,X1] :
      ( sK2(sK0,X0) != k9_subset_1(sK1,X0,X1)
      | v2_tex_2(X0,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k9_setfam_1(sK1))
      | ~ m1_subset_1(X0,k9_setfam_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f131,f58])).

fof(f131,plain,(
    ! [X0,X1] :
      ( sK2(sK0,X0) != k9_subset_1(sK1,X0,X1)
      | v2_tex_2(X0,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k9_setfam_1(sK1))
      | ~ m1_subset_1(X0,k9_setfam_1(sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f94,f60])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f73,f63,f63])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f225,plain,
    ( v3_pre_topc(sK2(sK0,sK1),sK0)
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f216,f203])).

fof(f203,plain,
    ( ! [X27] :
        ( v3_pre_topc(X27,sK0)
        | ~ m1_subset_1(X27,u1_pre_topc(sK0)) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f202,f125])).

fof(f202,plain,
    ( ! [X27] :
        ( ~ m1_subset_1(X27,k9_setfam_1(sK1))
        | v3_pre_topc(X27,sK0) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f201,f124])).

fof(f124,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f58,f116,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f201,plain,
    ( ! [X27] :
        ( ~ m1_subset_1(X27,k9_setfam_1(sK1))
        | v3_pre_topc(X27,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f200,f58])).

fof(f200,plain,
    ( ! [X27] :
        ( ~ m1_subset_1(X27,k9_setfam_1(sK1))
        | v3_pre_topc(X27,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f148,f116])).

fof(f148,plain,(
    ! [X27] :
      ( ~ m1_subset_1(X27,k9_setfam_1(sK1))
      | v3_pre_topc(X27,sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f103,f60])).

fof(f103,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f76,f63])).

fof(f76,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK4(X0),X0)
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f119,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f61,f115,f111])).

fof(f61,plain,
    ( v1_tdlat_3(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f118,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f62,f115,f111])).

fof(f62,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

%------------------------------------------------------------------------------
