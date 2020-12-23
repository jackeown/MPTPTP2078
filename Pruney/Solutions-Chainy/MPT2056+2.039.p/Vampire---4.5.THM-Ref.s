%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 232 expanded)
%              Number of leaves         :   28 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  341 ( 935 expanded)
%              Number of equality atoms :   47 ( 140 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f101,f106,f126,f148,f155,f192])).

fof(f192,plain,
    ( spl2_9
    | spl2_12
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl2_9
    | spl2_12
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f190,f105])).

fof(f105,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_9
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f190,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl2_12
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f187,f121])).

fof(f121,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f58,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f41,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f41,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f187,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | spl2_12
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f154,f183])).

fof(f183,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl2_12 ),
    inference(unit_resulting_resolution,[],[f147,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(resolution,[],[f115,f51])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k1_tarski(X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f49,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f147,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl2_12
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f154,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl2_13
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f155,plain,
    ( spl2_13
    | spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f133,f98,f88,f83,f73,f68,f63,f152])).

fof(f63,plain,
    ( spl2_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f68,plain,
    ( spl2_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f73,plain,
    ( spl2_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f83,plain,
    ( spl2_5
  <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f88,plain,
    ( spl2_6
  <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f98,plain,
    ( spl2_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f133,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0)))
    | spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f131,f127])).

fof(f127,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f100,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f53,f48])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f131,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))
    | spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f65,f70,f75,f90,f85,f100,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f47,f43,f43,f43,f43])).

fof(f43,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(f85,plain,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f90,plain,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f75,plain,
    ( ~ v1_xboole_0(sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f70,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f65,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f148,plain,
    ( ~ spl2_12
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | spl2_10 ),
    inference(avatar_split_clause,[],[f130,f123,f98,f93,f88,f83,f78,f73,f145])).

fof(f78,plain,
    ( spl2_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f93,plain,
    ( spl2_7
  <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f123,plain,
    ( spl2_10
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f130,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | spl2_10 ),
    inference(unit_resulting_resolution,[],[f80,f75,f90,f85,f95,f100,f125,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f44,f43,f43,f43,f43])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(f125,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f95,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f80,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f126,plain,
    ( ~ spl2_10
    | spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f114,f68,f63,f123])).

fof(f114,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f113,f109])).

fof(f109,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f70,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f113,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f65,f70,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f106,plain,(
    ~ spl2_9 ),
    inference(avatar_split_clause,[],[f39,f103])).

fof(f39,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f101,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f54,f98])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f30])).

fof(f96,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f57,f93])).

fof(f57,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f35,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f56,f88])).

fof(f56,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f36,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f55,f83])).

fof(f55,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f37,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f76,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (28313)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.42  % (28313)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f193,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f101,f106,f126,f148,f155,f192])).
% 0.19/0.42  fof(f192,plain,(
% 0.19/0.42    spl2_9 | spl2_12 | ~spl2_13),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f191])).
% 0.19/0.42  fof(f191,plain,(
% 0.19/0.42    $false | (spl2_9 | spl2_12 | ~spl2_13)),
% 0.19/0.42    inference(subsumption_resolution,[],[f190,f105])).
% 0.19/0.42  fof(f105,plain,(
% 0.19/0.42    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl2_9),
% 0.19/0.42    inference(avatar_component_clause,[],[f103])).
% 0.19/0.42  fof(f103,plain,(
% 0.19/0.42    spl2_9 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.19/0.42  fof(f190,plain,(
% 0.19/0.42    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (spl2_12 | ~spl2_13)),
% 0.19/0.42    inference(forward_demodulation,[],[f187,f121])).
% 0.19/0.42  fof(f121,plain,(
% 0.19/0.42    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.42    inference(backward_demodulation,[],[f58,f116])).
% 0.19/0.42  fof(f116,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f41,f51])).
% 0.19/0.42  fof(f51,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f31])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.42    inference(nnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f6])).
% 0.19/0.42  fof(f6,axiom,(
% 0.19/0.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.19/0.42  fof(f58,plain,(
% 0.19/0.42    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.19/0.42    inference(definition_unfolding,[],[f42,f48])).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.42  fof(f187,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k1_xboole_0) | (spl2_12 | ~spl2_13)),
% 0.19/0.42    inference(backward_demodulation,[],[f154,f183])).
% 0.19/0.42  fof(f183,plain,(
% 0.19/0.42    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl2_12),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f147,f149])).
% 0.19/0.42  fof(f149,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 = k3_xboole_0(X1,k1_tarski(X0))) )),
% 0.19/0.42    inference(resolution,[],[f115,f51])).
% 0.19/0.42  fof(f115,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,k1_tarski(X0)) | r2_hidden(X0,X1)) )),
% 0.19/0.42    inference(resolution,[],[f49,f50])).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.19/0.42  fof(f49,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,axiom,(
% 0.19/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.19/0.42  fof(f147,plain,(
% 0.19/0.42    ~r2_hidden(k1_xboole_0,sK1) | spl2_12),
% 0.19/0.42    inference(avatar_component_clause,[],[f145])).
% 0.19/0.42  fof(f145,plain,(
% 0.19/0.42    spl2_12 <=> r2_hidden(k1_xboole_0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.19/0.42  fof(f154,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0))) | ~spl2_13),
% 0.19/0.42    inference(avatar_component_clause,[],[f152])).
% 0.19/0.42  fof(f152,plain,(
% 0.19/0.42    spl2_13 <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0)))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.19/0.42  fof(f155,plain,(
% 0.19/0.42    spl2_13 | spl2_1 | ~spl2_2 | spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_8),
% 0.19/0.42    inference(avatar_split_clause,[],[f133,f98,f88,f83,f73,f68,f63,f152])).
% 0.19/0.42  fof(f63,plain,(
% 0.19/0.42    spl2_1 <=> v2_struct_0(sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.42  fof(f68,plain,(
% 0.19/0.42    spl2_2 <=> l1_struct_0(sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.42  fof(f73,plain,(
% 0.19/0.42    spl2_3 <=> v1_xboole_0(sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.42  fof(f83,plain,(
% 0.19/0.42    spl2_5 <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.42  fof(f88,plain,(
% 0.19/0.42    spl2_6 <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.19/0.42  fof(f98,plain,(
% 0.19/0.42    spl2_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.42  fof(f133,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0))) | (spl2_1 | ~spl2_2 | spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_8)),
% 0.19/0.42    inference(forward_demodulation,[],[f131,f127])).
% 0.19/0.42  fof(f127,plain,(
% 0.19/0.42    ( ! [X0] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ) | ~spl2_8),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f100,f61])).
% 0.19/0.42  fof(f61,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.19/0.42    inference(definition_unfolding,[],[f53,f48])).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f27])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.19/0.42  fof(f100,plain,(
% 0.19/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~spl2_8),
% 0.19/0.42    inference(avatar_component_clause,[],[f98])).
% 0.19/0.42  fof(f131,plain,(
% 0.19/0.42    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) | (spl2_1 | ~spl2_2 | spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_8)),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f65,f70,f75,f90,f85,f100,f60])).
% 0.19/0.42  fof(f60,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) | v2_struct_0(X0)) )),
% 0.19/0.42    inference(definition_unfolding,[],[f47,f43,f43,f43,f43])).
% 0.19/0.42  fof(f43,plain,(
% 0.19/0.42    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,axiom,(
% 0.19/0.42    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.42    inference(flattening,[],[f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,axiom,(
% 0.19/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).
% 0.19/0.42  fof(f85,plain,(
% 0.19/0.42    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~spl2_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f83])).
% 0.19/0.42  fof(f90,plain,(
% 0.19/0.42    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~spl2_6),
% 0.19/0.42    inference(avatar_component_clause,[],[f88])).
% 0.19/0.43  fof(f75,plain,(
% 0.19/0.43    ~v1_xboole_0(sK1) | spl2_3),
% 0.19/0.43    inference(avatar_component_clause,[],[f73])).
% 0.19/0.43  fof(f70,plain,(
% 0.19/0.43    l1_struct_0(sK0) | ~spl2_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f68])).
% 0.19/0.43  fof(f65,plain,(
% 0.19/0.43    ~v2_struct_0(sK0) | spl2_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f63])).
% 0.19/0.43  fof(f148,plain,(
% 0.19/0.43    ~spl2_12 | spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | spl2_10),
% 0.19/0.43    inference(avatar_split_clause,[],[f130,f123,f98,f93,f88,f83,f78,f73,f145])).
% 0.19/0.43  fof(f78,plain,(
% 0.19/0.43    spl2_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.43  fof(f93,plain,(
% 0.19/0.43    spl2_7 <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.19/0.43  fof(f123,plain,(
% 0.19/0.43    spl2_10 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.19/0.43  fof(f130,plain,(
% 0.19/0.43    ~r2_hidden(k1_xboole_0,sK1) | (spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | spl2_10)),
% 0.19/0.43    inference(unit_resulting_resolution,[],[f80,f75,f90,f85,f95,f100,f125,f59])).
% 0.19/0.43  fof(f59,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f44,f43,f43,f43,f43])).
% 0.19/0.43  fof(f44,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f19])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.19/0.43    inference(flattening,[],[f18])).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.19/0.43    inference(ennf_transformation,[],[f13])).
% 0.19/0.43  fof(f13,axiom,(
% 0.19/0.43    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 0.19/0.43  fof(f125,plain,(
% 0.19/0.43    ~v1_xboole_0(k2_struct_0(sK0)) | spl2_10),
% 0.19/0.43    inference(avatar_component_clause,[],[f123])).
% 0.19/0.43  fof(f95,plain,(
% 0.19/0.43    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~spl2_7),
% 0.19/0.43    inference(avatar_component_clause,[],[f93])).
% 0.19/0.43  fof(f80,plain,(
% 0.19/0.43    v1_xboole_0(k1_xboole_0) | ~spl2_4),
% 0.19/0.43    inference(avatar_component_clause,[],[f78])).
% 0.19/0.43  fof(f126,plain,(
% 0.19/0.43    ~spl2_10 | spl2_1 | ~spl2_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f114,f68,f63,f123])).
% 0.19/0.43  fof(f114,plain,(
% 0.19/0.43    ~v1_xboole_0(k2_struct_0(sK0)) | (spl2_1 | ~spl2_2)),
% 0.19/0.43    inference(forward_demodulation,[],[f113,f109])).
% 0.19/0.43  fof(f109,plain,(
% 0.19/0.43    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl2_2),
% 0.19/0.43    inference(unit_resulting_resolution,[],[f70,f45])).
% 0.19/0.43  fof(f45,plain,(
% 0.19/0.43    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f20])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.43    inference(ennf_transformation,[],[f9])).
% 0.19/0.43  fof(f9,axiom,(
% 0.19/0.43    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.43  fof(f113,plain,(
% 0.19/0.43    ~v1_xboole_0(u1_struct_0(sK0)) | (spl2_1 | ~spl2_2)),
% 0.19/0.43    inference(unit_resulting_resolution,[],[f65,f70,f46])).
% 0.19/0.43  fof(f46,plain,(
% 0.19/0.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f22])).
% 0.19/0.43  fof(f22,plain,(
% 0.19/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.43    inference(flattening,[],[f21])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.43    inference(ennf_transformation,[],[f10])).
% 0.19/0.43  fof(f10,axiom,(
% 0.19/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.19/0.43  fof(f106,plain,(
% 0.19/0.43    ~spl2_9),
% 0.19/0.43    inference(avatar_split_clause,[],[f39,f103])).
% 0.19/0.43  fof(f39,plain,(
% 0.19/0.43    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.43    inference(cnf_transformation,[],[f30])).
% 0.19/0.43  fof(f30,plain,(
% 0.19/0.43    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f29,f28])).
% 0.19/0.43  fof(f28,plain,(
% 0.19/0.43    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f29,plain,(
% 0.19/0.43    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.19/0.43    inference(flattening,[],[f16])).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.19/0.43    inference(ennf_transformation,[],[f15])).
% 0.19/0.43  fof(f15,negated_conjecture,(
% 0.19/0.43    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.19/0.43    inference(negated_conjecture,[],[f14])).
% 0.19/0.43  fof(f14,conjecture,(
% 0.19/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.19/0.43  fof(f101,plain,(
% 0.19/0.43    spl2_8),
% 0.19/0.43    inference(avatar_split_clause,[],[f54,f98])).
% 0.19/0.43  fof(f54,plain,(
% 0.19/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.19/0.43    inference(definition_unfolding,[],[f38,f43])).
% 0.19/0.43  fof(f38,plain,(
% 0.19/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.19/0.43    inference(cnf_transformation,[],[f30])).
% 0.19/0.43  fof(f96,plain,(
% 0.19/0.43    spl2_7),
% 0.19/0.43    inference(avatar_split_clause,[],[f57,f93])).
% 0.19/0.43  fof(f57,plain,(
% 0.19/0.43    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.19/0.43    inference(definition_unfolding,[],[f35,f43])).
% 0.19/0.43  fof(f35,plain,(
% 0.19/0.43    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.19/0.43    inference(cnf_transformation,[],[f30])).
% 0.19/0.43  fof(f91,plain,(
% 0.19/0.43    spl2_6),
% 0.19/0.43    inference(avatar_split_clause,[],[f56,f88])).
% 0.19/0.43  fof(f56,plain,(
% 0.19/0.43    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.19/0.43    inference(definition_unfolding,[],[f36,f43])).
% 0.19/0.43  fof(f36,plain,(
% 0.19/0.43    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.19/0.43    inference(cnf_transformation,[],[f30])).
% 0.19/0.43  fof(f86,plain,(
% 0.19/0.43    spl2_5),
% 0.19/0.43    inference(avatar_split_clause,[],[f55,f83])).
% 0.19/0.43  fof(f55,plain,(
% 0.19/0.43    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.19/0.43    inference(definition_unfolding,[],[f37,f43])).
% 0.19/0.43  fof(f37,plain,(
% 0.19/0.43    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.19/0.43    inference(cnf_transformation,[],[f30])).
% 0.19/0.43  fof(f81,plain,(
% 0.19/0.43    spl2_4),
% 0.19/0.43    inference(avatar_split_clause,[],[f40,f78])).
% 0.19/0.43  fof(f40,plain,(
% 0.19/0.43    v1_xboole_0(k1_xboole_0)),
% 0.19/0.43    inference(cnf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    v1_xboole_0(k1_xboole_0)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.43  fof(f76,plain,(
% 0.19/0.43    ~spl2_3),
% 0.19/0.43    inference(avatar_split_clause,[],[f34,f73])).
% 0.19/0.43  fof(f34,plain,(
% 0.19/0.43    ~v1_xboole_0(sK1)),
% 0.19/0.43    inference(cnf_transformation,[],[f30])).
% 0.19/0.43  fof(f71,plain,(
% 0.19/0.43    spl2_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f33,f68])).
% 0.19/0.43  fof(f33,plain,(
% 0.19/0.43    l1_struct_0(sK0)),
% 0.19/0.43    inference(cnf_transformation,[],[f30])).
% 0.19/0.43  fof(f66,plain,(
% 0.19/0.43    ~spl2_1),
% 0.19/0.43    inference(avatar_split_clause,[],[f32,f63])).
% 0.19/0.43  fof(f32,plain,(
% 0.19/0.43    ~v2_struct_0(sK0)),
% 0.19/0.43    inference(cnf_transformation,[],[f30])).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (28313)------------------------------
% 0.19/0.43  % (28313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (28313)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (28313)Memory used [KB]: 10746
% 0.19/0.43  % (28313)Time elapsed: 0.012 s
% 0.19/0.43  % (28313)------------------------------
% 0.19/0.43  % (28313)------------------------------
% 0.19/0.43  % (28296)Success in time 0.077 s
%------------------------------------------------------------------------------
