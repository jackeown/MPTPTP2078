%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1876+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:49 EST 2020

% Result     : Theorem 10.23s
% Output     : Refutation 10.23s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 766 expanded)
%              Number of leaves         :   41 ( 223 expanded)
%              Depth                    :   21
%              Number of atoms          :  759 (4884 expanded)
%              Number of equality atoms :  106 ( 184 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35648,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f122,f133,f231,f1413,f1513,f1785,f3688,f3689,f3690,f8367,f8407,f19606,f35596,f35645])).

fof(f35645,plain,
    ( ~ spl7_1
    | ~ spl7_279
    | ~ spl7_332
    | spl7_334 ),
    inference(avatar_contradiction_clause,[],[f35644])).

fof(f35644,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_279
    | ~ spl7_332
    | spl7_334 ),
    inference(subsumption_resolution,[],[f8380,f8350])).

fof(f8350,plain,
    ( k1_xboole_0 != k1_tarski(sK5(sK1))
    | spl7_334 ),
    inference(avatar_component_clause,[],[f8349])).

fof(f8349,plain,
    ( spl7_334
  <=> k1_xboole_0 = k1_tarski(sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_334])])).

fof(f8380,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK1))
    | ~ spl7_1
    | ~ spl7_279
    | ~ spl7_332 ),
    inference(forward_demodulation,[],[f8379,f7374])).

fof(f7374,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(resolution,[],[f7372,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f7372,plain,(
    r1_tarski(k1_xboole_0,sK1) ),
    inference(superposition,[],[f7363,f112])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f7363,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK2(sK1),X0),sK1) ),
    inference(superposition,[],[f7345,f111])).

fof(f111,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f7345,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK2(sK1)),sK1) ),
    inference(forward_demodulation,[],[f4605,f422])).

fof(f422,plain,(
    ! [X1] : k9_subset_1(sK1,X1,sK2(sK1)) = k3_xboole_0(X1,sK2(sK1)) ),
    inference(resolution,[],[f202,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f202,plain,(
    m1_subset_1(sK2(sK1),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f77,f81])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(sK2(X0))
        & ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_zfmisc_1(sK2(X0))
        & ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_tex_2)).

fof(f77,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f4605,plain,(
    ! [X0] : r1_tarski(k9_subset_1(sK1,X0,sK2(sK1)),sK1) ),
    inference(resolution,[],[f421,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f421,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(sK1,X0,sK2(sK1)),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f202,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f8379,plain,
    ( k1_tarski(sK5(sK1)) = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl7_1
    | ~ spl7_279
    | ~ spl7_332 ),
    inference(forward_demodulation,[],[f8378,f111])).

fof(f8378,plain,
    ( k1_tarski(sK5(sK1)) = k3_xboole_0(sK1,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_279
    | ~ spl7_332 ),
    inference(forward_demodulation,[],[f8368,f7486])).

fof(f7486,plain,
    ( k1_xboole_0 = sK4(sK0,sK1,sK5(sK1))
    | ~ spl7_279 ),
    inference(avatar_component_clause,[],[f7484])).

fof(f7484,plain,
    ( spl7_279
  <=> k1_xboole_0 = sK4(sK0,sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_279])])).

fof(f8368,plain,
    ( k1_tarski(sK5(sK1)) = k3_xboole_0(sK1,sK4(sK0,sK1,sK5(sK1)))
    | ~ spl7_1
    | ~ spl7_332 ),
    inference(resolution,[],[f8334,f1599])).

fof(f1599,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | k1_tarski(X2) = k3_xboole_0(sK1,sK4(sK0,sK1,X2)) )
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f1598,f111])).

fof(f1598,plain,
    ( ! [X2] :
        ( k1_tarski(X2) = k3_xboole_0(sK4(sK0,sK1,X2),sK1)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f1597,f899])).

fof(f899,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),sK1,X5) = k3_xboole_0(X5,sK1) ),
    inference(forward_demodulation,[],[f298,f297])).

fof(f297,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK1) = k3_xboole_0(X4,sK1) ),
    inference(resolution,[],[f78,f93])).

fof(f78,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f298,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X5) ),
    inference(resolution,[],[f78,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f1597,plain,
    ( ! [X2] :
        ( k1_tarski(X2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X2))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f1596,f299])).

fof(f299,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK1)
      | m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f78,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f1596,plain,
    ( ! [X2] :
        ( k1_tarski(X2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X2))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f1595,f76])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f1595,plain,
    ( ! [X2] :
        ( k1_tarski(X2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X2))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f1578,f115])).

fof(f115,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl7_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1578,plain,(
    ! [X2] :
      ( k1_tarski(X2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X2))
      | ~ r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v2_tex_2(sK1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f78,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2))
                & v3_pre_topc(sK4(X0,X1,X2),X0)
                & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2))
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

fof(f8334,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl7_332 ),
    inference(avatar_component_clause,[],[f8333])).

fof(f8333,plain,
    ( spl7_332
  <=> r2_hidden(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_332])])).

fof(f35596,plain,
    ( ~ spl7_1
    | ~ spl7_16
    | ~ spl7_75
    | ~ spl7_78
    | spl7_279 ),
    inference(avatar_contradiction_clause,[],[f35595])).

fof(f35595,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_75
    | ~ spl7_78
    | spl7_279 ),
    inference(subsumption_resolution,[],[f35594,f2070])).

fof(f2070,plain,
    ( sK1 != k1_tarski(sK5(sK1))
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f2069,f77])).

fof(f2069,plain,
    ( sK1 != k1_tarski(sK5(sK1))
    | v1_xboole_0(sK1)
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f2068,f98])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f8,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f2068,plain,
    ( sK1 != k1_tarski(sK5(sK1))
    | ~ m1_subset_1(sK5(sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ spl7_16 ),
    inference(superposition,[],[f1820,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f1820,plain,
    ( sK1 != k6_domain_1(sK1,sK5(sK1))
    | ~ spl7_16 ),
    inference(resolution,[],[f223,f98])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | sK1 != k6_domain_1(sK1,X0) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl7_16
  <=> ! [X0] :
        ( sK1 != k6_domain_1(sK1,X0)
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f35594,plain,
    ( sK1 = k1_tarski(sK5(sK1))
    | ~ spl7_1
    | ~ spl7_75
    | ~ spl7_78
    | spl7_279 ),
    inference(forward_demodulation,[],[f35593,f371])).

fof(f371,plain,(
    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f295,f110])).

fof(f295,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f78,f99])).

fof(f35593,plain,
    ( k3_xboole_0(sK1,u1_struct_0(sK0)) = k1_tarski(sK5(sK1))
    | ~ spl7_1
    | ~ spl7_75
    | ~ spl7_78
    | spl7_279 ),
    inference(forward_demodulation,[],[f9118,f25805])).

fof(f25805,plain,
    ( u1_struct_0(sK0) = sK4(sK0,sK1,sK5(sK1))
    | ~ spl7_75
    | ~ spl7_78
    | spl7_279 ),
    inference(subsumption_resolution,[],[f25804,f74])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f25804,plain,
    ( u1_struct_0(sK0) = sK4(sK0,sK1,sK5(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_75
    | ~ spl7_78
    | spl7_279 ),
    inference(subsumption_resolution,[],[f25803,f76])).

fof(f25803,plain,
    ( u1_struct_0(sK0) = sK4(sK0,sK1,sK5(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_75
    | ~ spl7_78
    | spl7_279 ),
    inference(subsumption_resolution,[],[f25802,f75])).

fof(f75,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f25802,plain,
    ( u1_struct_0(sK0) = sK4(sK0,sK1,sK5(sK1))
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_75
    | ~ spl7_78
    | spl7_279 ),
    inference(subsumption_resolution,[],[f25801,f6526])).

fof(f6526,plain,
    ( v3_pre_topc(sK4(sK0,sK1,sK5(sK1)),sK0)
    | ~ spl7_75 ),
    inference(resolution,[],[f2043,f98])).

fof(f2043,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v3_pre_topc(sK4(sK0,sK1,X0),sK0) )
    | ~ spl7_75 ),
    inference(resolution,[],[f1438,f210])).

fof(f210,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(resolution,[],[f77,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f1438,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | v3_pre_topc(sK4(sK0,sK1,X1),sK0) )
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f1437])).

fof(f1437,plain,
    ( spl7_75
  <=> ! [X1] :
        ( v3_pre_topc(sK4(sK0,sK1,X1),sK0)
        | ~ r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f25801,plain,
    ( u1_struct_0(sK0) = sK4(sK0,sK1,sK5(sK1))
    | ~ v3_pre_topc(sK4(sK0,sK1,sK5(sK1)),sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_78
    | spl7_279 ),
    inference(subsumption_resolution,[],[f25786,f7485])).

fof(f7485,plain,
    ( k1_xboole_0 != sK4(sK0,sK1,sK5(sK1))
    | spl7_279 ),
    inference(avatar_component_clause,[],[f7484])).

fof(f25786,plain,
    ( u1_struct_0(sK0) = sK4(sK0,sK1,sK5(sK1))
    | k1_xboole_0 = sK4(sK0,sK1,sK5(sK1))
    | ~ v3_pre_topc(sK4(sK0,sK1,sK5(sK1)),sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_78 ),
    inference(resolution,[],[f21875,f100])).

fof(f100,plain,(
    ! [X2,X0] :
      ( u1_struct_0(X0) = X2
      | k1_xboole_0 = X2
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ( u1_struct_0(X0) != sK6(X0)
            & k1_xboole_0 != sK6(X0)
            & v3_pre_topc(sK6(X0),X0)
            & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f70,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( u1_struct_0(X0) != X1
          & k1_xboole_0 != X1
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( u1_struct_0(X0) != sK6(X0)
        & k1_xboole_0 != sK6(X0)
        & v3_pre_topc(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( u1_struct_0(X0) = X1
              | k1_xboole_0 = X1
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( u1_struct_0(X0) != X1
                & k1_xboole_0 != X1
                & v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tdlat_3)).

fof(f21875,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK5(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_78 ),
    inference(resolution,[],[f20002,f98])).

fof(f20002,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_78 ),
    inference(resolution,[],[f1467,f210])).

fof(f1467,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f1466,plain,
    ( spl7_78
  <=> ! [X0] :
        ( m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f9118,plain,
    ( k1_tarski(sK5(sK1)) = k3_xboole_0(sK1,sK4(sK0,sK1,sK5(sK1)))
    | ~ spl7_1 ),
    inference(resolution,[],[f2995,f98])).

fof(f2995,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_tarski(X0) = k3_xboole_0(sK1,sK4(sK0,sK1,X0)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f1599,f210])).

fof(f19606,plain,
    ( ~ spl7_79
    | spl7_78
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f2448,f114,f1466,f1470])).

fof(f1470,plain,
    ( spl7_79
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f2448,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f2447,f91])).

fof(f2447,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f2444,f76])).

fof(f2444,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_1 ),
    inference(resolution,[],[f115,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f8407,plain,(
    ~ spl7_334 ),
    inference(avatar_contradiction_clause,[],[f8406])).

fof(f8406,plain,
    ( $false
    | ~ spl7_334 ),
    inference(subsumption_resolution,[],[f8405,f108])).

fof(f108,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f8405,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_334 ),
    inference(superposition,[],[f107,f8351])).

fof(f8351,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK1))
    | ~ spl7_334 ),
    inference(avatar_component_clause,[],[f8349])).

fof(f107,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f8367,plain,(
    spl7_332 ),
    inference(avatar_contradiction_clause,[],[f8366])).

fof(f8366,plain,
    ( $false
    | spl7_332 ),
    inference(subsumption_resolution,[],[f8365,f98])).

fof(f8365,plain,
    ( ~ m1_subset_1(sK5(sK1),sK1)
    | spl7_332 ),
    inference(subsumption_resolution,[],[f8361,f77])).

fof(f8361,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5(sK1),sK1)
    | spl7_332 ),
    inference(resolution,[],[f8335,f97])).

fof(f8335,plain,
    ( ~ r2_hidden(sK5(sK1),sK1)
    | spl7_332 ),
    inference(avatar_component_clause,[],[f8333])).

fof(f3690,plain,
    ( spl7_16
    | spl7_2 ),
    inference(avatar_split_clause,[],[f3684,f118,f222])).

fof(f118,plain,
    ( spl7_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f3684,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK1)
      | sK1 != k6_domain_1(sK1,X0)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f77,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK3(X0)) = X0
            & m1_subset_1(sK3(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f62,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK3(X0)) = X0
        & m1_subset_1(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f3689,plain,
    ( ~ spl7_2
    | spl7_15 ),
    inference(avatar_split_clause,[],[f3683,f217,f118])).

fof(f217,plain,
    ( spl7_15
  <=> sK1 = k6_domain_1(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f3683,plain,
    ( sK1 = k6_domain_1(sK1,sK3(sK1))
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f77,f85])).

fof(f85,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK3(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f3688,plain,
    ( ~ spl7_2
    | spl7_14 ),
    inference(avatar_split_clause,[],[f3682,f212,f118])).

fof(f212,plain,
    ( spl7_14
  <=> m1_subset_1(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f3682,plain,
    ( m1_subset_1(sK3(sK1),sK1)
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f77,f84])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1785,plain,(
    spl7_79 ),
    inference(avatar_contradiction_clause,[],[f1784])).

fof(f1784,plain,
    ( $false
    | spl7_79 ),
    inference(subsumption_resolution,[],[f1472,f78])).

fof(f1472,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_79 ),
    inference(avatar_component_clause,[],[f1470])).

fof(f1513,plain,
    ( ~ spl7_79
    | spl7_75
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f1512,f114,f1437,f1470])).

fof(f1512,plain,
    ( ! [X1] :
        ( v3_pre_topc(sK4(sK0,sK1,X1),sK0)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f1511,f91])).

fof(f1511,plain,
    ( ! [X1] :
        ( v3_pre_topc(sK4(sK0,sK1,X1),sK0)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f1506,f76])).

fof(f1506,plain,
    ( ! [X1] :
        ( v3_pre_topc(sK4(sK0,sK1,X1),sK0)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_1 ),
    inference(resolution,[],[f115,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f1413,plain,
    ( spl7_1
    | spl7_4
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f1412])).

fof(f1412,plain,
    ( $false
    | spl7_1
    | spl7_4
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1411,f116])).

fof(f116,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1411,plain,
    ( v2_tex_2(sK1,sK0)
    | spl7_4
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f1410,f504])).

fof(f504,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f503,f77])).

fof(f503,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | v1_xboole_0(sK1)
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f498,f214])).

fof(f214,plain,
    ( m1_subset_1(sK3(sK1),sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f212])).

fof(f498,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ m1_subset_1(sK3(sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ spl7_15 ),
    inference(superposition,[],[f219,f96])).

fof(f219,plain,
    ( sK1 = k6_domain_1(sK1,sK3(sK1))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f217])).

fof(f1410,plain,
    ( v2_tex_2(k1_tarski(sK3(sK1)),sK0)
    | spl7_4
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f1409,f132])).

fof(f132,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_4
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1409,plain,
    ( v2_tex_2(k1_tarski(sK3(sK1)),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f1375,f577])).

fof(f577,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl7_14 ),
    inference(resolution,[],[f299,f360])).

fof(f360,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f356,f77])).

fof(f356,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ spl7_14 ),
    inference(resolution,[],[f214,f97])).

fof(f1375,plain,
    ( v2_tex_2(k1_tarski(sK3(sK1)),sK0)
    | ~ m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_14 ),
    inference(superposition,[],[f701,f96])).

fof(f701,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f700,f73])).

fof(f73,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f700,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f699,f74])).

fof(f699,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f685,f76])).

fof(f685,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_14 ),
    inference(resolution,[],[f577,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f231,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f229,f76])).

fof(f229,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_3 ),
    inference(resolution,[],[f128,f109])).

fof(f109,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f128,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f133,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f123,f130,f126])).

fof(f123,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f73,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f122,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f79,f118,f114])).

fof(f79,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f121,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f80,f118,f114])).

fof(f80,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

%------------------------------------------------------------------------------
