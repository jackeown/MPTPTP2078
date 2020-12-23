%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t84_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:33 EDT 2019

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 453 expanded)
%              Number of leaves         :   32 ( 140 expanded)
%              Depth                    :   18
%              Number of atoms          :  424 (1525 expanded)
%              Number of equality atoms :  100 ( 472 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3565,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f135,f791,f796,f1191,f1448,f1495,f1513,f1523,f1537,f1584,f1590,f1648,f3558])).

fof(f3558,plain,
    ( ~ spl5_2
    | spl5_75
    | ~ spl5_142 ),
    inference(avatar_contradiction_clause,[],[f3557])).

fof(f3557,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_75
    | ~ spl5_142 ),
    inference(subsumption_resolution,[],[f3556,f269])).

fof(f269,plain,(
    ! [X4] : k3_subset_1(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f266,f89])).

fof(f89,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',t3_boole)).

fof(f266,plain,(
    ! [X4] : k3_subset_1(X4,k1_xboole_0) = k4_xboole_0(X4,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f262])).

fof(f262,plain,(
    ! [X4] :
      ( k1_xboole_0 != k1_xboole_0
      | k3_subset_1(X4,k1_xboole_0) = k4_xboole_0(X4,k1_xboole_0) ) ),
    inference(superposition,[],[f242,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',t4_boole)).

fof(f242,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X0)
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f198,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',t37_xboole_1)).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f106,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',t3_subset)).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',d5_subset_1)).

fof(f3556,plain,
    ( u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_75
    | ~ spl5_142 ),
    inference(forward_demodulation,[],[f3555,f130])).

fof(f130,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_2
  <=> k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f3555,plain,
    ( u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl5_75
    | ~ spl5_142 ),
    inference(subsumption_resolution,[],[f3538,f85])).

fof(f85,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,
    ( ( k1_tops_1(sK0,sK1) != k1_xboole_0
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_tops_1(sK0,sK1) = k1_xboole_0
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f70,f72,f71])).

fof(f71,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_tops_1(X0,X1) != k1_xboole_0
              | ~ v2_tops_1(X1,X0) )
            & ( k1_tops_1(X0,X1) = k1_xboole_0
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_tops_1(sK0,X1) != k1_xboole_0
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_tops_1(sK0,X1) = k1_xboole_0
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k1_tops_1(X0,X1) != k1_xboole_0
            | ~ v2_tops_1(X1,X0) )
          & ( k1_tops_1(X0,X1) = k1_xboole_0
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k1_tops_1(X0,sK1) != k1_xboole_0
          | ~ v2_tops_1(sK1,X0) )
        & ( k1_tops_1(X0,sK1) = k1_xboole_0
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_tops_1(X0,X1) != k1_xboole_0
            | ~ v2_tops_1(X1,X0) )
          & ( k1_tops_1(X0,X1) = k1_xboole_0
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_tops_1(X0,X1) != k1_xboole_0
            | ~ v2_tops_1(X1,X0) )
          & ( k1_tops_1(X0,X1) = k1_xboole_0
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_tops_1(X0,X1) = k1_xboole_0 )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_tops_1(X0,X1) = k1_xboole_0 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',t84_tops_1)).

fof(f3538,plain,
    ( u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_75
    | ~ spl5_142 ),
    inference(superposition,[],[f1651,f3345])).

fof(f3345,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3344,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',dt_k3_subset_1)).

fof(f3344,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3329,f84])).

fof(f84,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f3329,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f1616,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',dt_k2_pre_topc)).

fof(f1616,plain,(
    ! [X4] :
      ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X4)),k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X4)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f105,f1349])).

fof(f1349,plain,(
    ! [X0] :
      ( k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f95,f84])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',d1_tops_1)).

fof(f105,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',involutiveness_k3_subset_1)).

fof(f1651,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl5_75
    | ~ spl5_142 ),
    inference(forward_demodulation,[],[f790,f1583])).

fof(f1583,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_142 ),
    inference(avatar_component_clause,[],[f1582])).

fof(f1582,plain,
    ( spl5_142
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f790,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f789])).

fof(f789,plain,
    ( spl5_75
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f1648,plain,
    ( spl5_3
    | ~ spl5_74
    | ~ spl5_142 ),
    inference(avatar_contradiction_clause,[],[f1647])).

fof(f1647,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_74
    | ~ spl5_142 ),
    inference(subsumption_resolution,[],[f1646,f133])).

fof(f133,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_3
  <=> k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1646,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | ~ spl5_74
    | ~ spl5_142 ),
    inference(forward_demodulation,[],[f1645,f287])).

fof(f287,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(subsumption_resolution,[],[f285,f90])).

fof(f285,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_subset_1(X0,X0)
      | k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f283,f114])).

fof(f283,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | k1_xboole_0 = k3_subset_1(X0,X0) ) ),
    inference(resolution,[],[f271,f113])).

fof(f271,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | k1_xboole_0 = k3_subset_1(X0,X0) ) ),
    inference(superposition,[],[f105,f269])).

fof(f1645,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_74
    | ~ spl5_142 ),
    inference(subsumption_resolution,[],[f1642,f85])).

fof(f1642,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_74
    | ~ spl5_142 ),
    inference(superposition,[],[f1349,f1630])).

fof(f1630,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl5_74
    | ~ spl5_142 ),
    inference(forward_demodulation,[],[f787,f1583])).

fof(f787,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f786])).

fof(f786,plain,
    ( spl5_74
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f1590,plain,
    ( ~ spl5_42
    | spl5_139 ),
    inference(avatar_contradiction_clause,[],[f1589])).

fof(f1589,plain,
    ( $false
    | ~ spl5_42
    | ~ spl5_139 ),
    inference(subsumption_resolution,[],[f1585,f523])).

fof(f523,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f522])).

fof(f522,plain,
    ( spl5_42
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f1585,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl5_139 ),
    inference(resolution,[],[f1571,f92])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',dt_k2_struct_0)).

fof(f1571,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_139 ),
    inference(avatar_component_clause,[],[f1570])).

fof(f1570,plain,
    ( spl5_139
  <=> ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f1584,plain,
    ( ~ spl5_139
    | spl5_142
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f1577,f1438,f1582,f1570])).

fof(f1438,plain,
    ( spl5_122
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f1577,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f1564,f269])).

fof(f1564,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_122 ),
    inference(superposition,[],[f105,f1439])).

fof(f1439,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f1438])).

fof(f1537,plain,
    ( ~ spl5_42
    | spl5_121 ),
    inference(avatar_contradiction_clause,[],[f1536])).

fof(f1536,plain,
    ( $false
    | ~ spl5_42
    | ~ spl5_121 ),
    inference(subsumption_resolution,[],[f1534,f302])).

fof(f302,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f300,f90])).

fof(f300,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f298,f114])).

fof(f298,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | k1_xboole_0 = k4_xboole_0(X1,X1) ) ),
    inference(resolution,[],[f294,f113])).

fof(f294,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(forward_demodulation,[],[f280,f287])).

fof(f280,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f272,f106])).

fof(f272,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f104,f269])).

fof(f1534,plain,
    ( k1_xboole_0 != k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_42
    | ~ spl5_121 ),
    inference(resolution,[],[f1520,f114])).

fof(f1520,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_42
    | ~ spl5_121 ),
    inference(subsumption_resolution,[],[f1519,f523])).

fof(f1519,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl5_121 ),
    inference(superposition,[],[f1449,f91])).

fof(f91,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',d3_struct_0)).

fof(f1449,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl5_121 ),
    inference(resolution,[],[f1433,f113])).

fof(f1433,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_121 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f1432,plain,
    ( spl5_121
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f1523,plain,
    ( ~ spl5_73
    | spl5_74
    | ~ spl5_132 ),
    inference(avatar_split_clause,[],[f1522,f1493,f786,f783])).

fof(f783,plain,
    ( spl5_73
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f1493,plain,
    ( spl5_132
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f1522,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_132 ),
    inference(subsumption_resolution,[],[f1521,f84])).

fof(f1521,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_132 ),
    inference(resolution,[],[f1494,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',d3_tops_1)).

fof(f1494,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_132 ),
    inference(avatar_component_clause,[],[f1493])).

fof(f1513,plain,(
    spl5_131 ),
    inference(avatar_contradiction_clause,[],[f1512])).

fof(f1512,plain,
    ( $false
    | ~ spl5_131 ),
    inference(subsumption_resolution,[],[f1488,f85])).

fof(f1488,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_131 ),
    inference(avatar_component_clause,[],[f1487])).

fof(f1487,plain,
    ( spl5_131
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f1495,plain,
    ( ~ spl5_131
    | spl5_132
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f1482,f123,f1493,f1487])).

fof(f123,plain,
    ( spl5_0
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f1482,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0 ),
    inference(subsumption_resolution,[],[f1481,f84])).

fof(f1481,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(resolution,[],[f124,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',d4_tops_1)).

fof(f124,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f123])).

fof(f1448,plain,
    ( ~ spl5_121
    | spl5_122
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1425,f522,f1438,f1432])).

fof(f1425,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_42 ),
    inference(superposition,[],[f144,f1200])).

fof(f1200,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) = k4_xboole_0(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl5_42 ),
    inference(resolution,[],[f523,f202])).

fof(f202,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | k3_subset_1(u1_struct_0(X5),k2_struct_0(X5)) = k4_xboole_0(u1_struct_0(X5),k2_struct_0(X5)) ) ),
    inference(resolution,[],[f106,f92])).

fof(f144,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k4_xboole_0(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f115,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f1191,plain,(
    spl5_43 ),
    inference(avatar_contradiction_clause,[],[f1190])).

fof(f1190,plain,
    ( $false
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f1189,f84])).

fof(f1189,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_43 ),
    inference(resolution,[],[f526,f94])).

fof(f94,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t84_tops_1.p',dt_l1_pre_topc)).

fof(f526,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f525])).

fof(f525,plain,
    ( spl5_43
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f796,plain,(
    spl5_73 ),
    inference(avatar_contradiction_clause,[],[f795])).

fof(f795,plain,
    ( $false
    | ~ spl5_73 ),
    inference(subsumption_resolution,[],[f792,f85])).

fof(f792,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_73 ),
    inference(resolution,[],[f784,f104])).

fof(f784,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f783])).

fof(f791,plain,
    ( ~ spl5_73
    | ~ spl5_75
    | spl5_1 ),
    inference(avatar_split_clause,[],[f778,f126,f789,f783])).

fof(f126,plain,
    ( spl5_1
  <=> ~ v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f778,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f777,f84])).

fof(f777,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f776,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f776,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f773,f85])).

fof(f773,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f771,f127])).

fof(f127,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f771,plain,(
    ! [X0] :
      ( v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f99,f84])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f135,plain,
    ( spl5_0
    | spl5_2 ),
    inference(avatar_split_clause,[],[f86,f129,f123])).

fof(f86,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f134,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f87,f132,f126])).

fof(f87,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f73])).
%------------------------------------------------------------------------------
