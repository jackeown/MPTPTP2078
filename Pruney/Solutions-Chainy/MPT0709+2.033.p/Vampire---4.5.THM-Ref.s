%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 214 expanded)
%              Number of leaves         :   29 (  95 expanded)
%              Depth                    :    8
%              Number of atoms          :  379 ( 674 expanded)
%              Number of equality atoms :   63 ( 105 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f872,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f106,f112,f129,f238,f270,f299,f366,f399,f598,f627,f775,f871])).

fof(f871,plain,
    ( ~ spl2_6
    | ~ spl2_7
    | spl2_1
    | ~ spl2_28
    | ~ spl2_32
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f870,f772,f297,f268,f77,f109,f103])).

fof(f103,plain,
    ( spl2_6
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f109,plain,
    ( spl2_7
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f77,plain,
    ( spl2_1
  <=> sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f268,plain,
    ( spl2_28
  <=> ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f297,plain,
    ( spl2_32
  <=> ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f772,plain,
    ( spl2_88
  <=> r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f870,plain,
    ( sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_28
    | ~ spl2_32
    | ~ spl2_88 ),
    inference(forward_demodulation,[],[f869,f269])).

fof(f269,plain,
    ( ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f268])).

fof(f869,plain,
    ( sK0 = k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_32
    | ~ spl2_88 ),
    inference(forward_demodulation,[],[f823,f298])).

fof(f298,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f297])).

fof(f823,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_88 ),
    inference(resolution,[],[f774,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f774,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1)))
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f772])).

fof(f775,plain,
    ( spl2_88
    | ~ spl2_61
    | ~ spl2_69 ),
    inference(avatar_split_clause,[],[f766,f624,f560,f772])).

fof(f560,plain,
    ( spl2_61
  <=> r1_tarski(sK0,k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f624,plain,
    ( spl2_69
  <=> k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f766,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1)))
    | ~ spl2_61
    | ~ spl2_69 ),
    inference(backward_demodulation,[],[f562,f626])).

fof(f626,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f624])).

fof(f562,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))))
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f560])).

fof(f627,plain,
    ( ~ spl2_5
    | spl2_69
    | ~ spl2_4
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f622,f297,f92,f624,f97])).

fof(f97,plain,
    ( spl2_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f92,plain,
    ( spl2_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f622,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl2_4
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f605,f298])).

fof(f605,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f146,f94])).

fof(f94,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f146,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f54,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f598,plain,
    ( spl2_61
    | ~ spl2_3
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f557,f396,f87,f560])).

fof(f87,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f396,plain,
    ( spl2_47
  <=> r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f557,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))))
    | ~ spl2_3
    | ~ spl2_47 ),
    inference(resolution,[],[f398,f176])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK1),X0)
        | r1_tarski(sK0,X0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f70,f89])).

fof(f89,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f398,plain,
    ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f396])).

fof(f399,plain,
    ( spl2_47
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f394,f363,f125,f97,f396])).

fof(f125,plain,
    ( spl2_9
  <=> k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f363,plain,
    ( spl2_42
  <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f394,plain,
    ( r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))))
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_42 ),
    inference(forward_demodulation,[],[f367,f127])).

fof(f127,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f367,plain,
    ( r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))))
    | ~ spl2_5
    | ~ spl2_42 ),
    inference(unit_resulting_resolution,[],[f99,f365,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f365,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f363])).

fof(f99,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f366,plain,
    ( ~ spl2_6
    | ~ spl2_7
    | ~ spl2_5
    | ~ spl2_4
    | spl2_42
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f361,f234,f363,f92,f97,f109,f103])).

fof(f234,plain,
    ( spl2_24
  <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f361,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_24 ),
    inference(trivial_inequality_removal,[],[f360])).

fof(f360,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f359,f51])).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f359,plain,
    ( k1_relat_1(sK1) != k1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_24 ),
    inference(superposition,[],[f59,f236])).

fof(f236,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f234])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f299,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_32
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f295,f82,f297,f92,f97])).

fof(f82,plain,
    ( spl2_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f295,plain,
    ( ! [X0] :
        ( k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2 ),
    inference(resolution,[],[f64,f84])).

fof(f84,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f270,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_28
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f266,f82,f268,f92,f97])).

fof(f266,plain,
    ( ! [X0] :
        ( k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2 ),
    inference(resolution,[],[f63,f84])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f238,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_24
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f232,f82,f234,f92,f97])).

fof(f232,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f57,f84])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f129,plain,
    ( spl2_9
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f116,f97,f125])).

fof(f116,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl2_5 ),
    inference(resolution,[],[f53,f99])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f112,plain,
    ( spl2_7
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f107,f97,f92,f109])).

fof(f107,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f99,f94,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f106,plain,
    ( spl2_6
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f101,f97,f92,f103])).

fof(f101,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f99,f94,f55])).

fof(f100,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f45,f97])).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f95,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f47,f87])).

fof(f47,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f48,f82])).

fof(f48,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f49,f77])).

fof(f49,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (1928)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.44  % (1928)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f872,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f106,f112,f129,f238,f270,f299,f366,f399,f598,f627,f775,f871])).
% 0.19/0.44  fof(f871,plain,(
% 0.19/0.44    ~spl2_6 | ~spl2_7 | spl2_1 | ~spl2_28 | ~spl2_32 | ~spl2_88),
% 0.19/0.44    inference(avatar_split_clause,[],[f870,f772,f297,f268,f77,f109,f103])).
% 0.19/0.44  fof(f103,plain,(
% 0.19/0.44    spl2_6 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.19/0.44  fof(f109,plain,(
% 0.19/0.44    spl2_7 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.19/0.44  fof(f77,plain,(
% 0.19/0.44    spl2_1 <=> sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.44  fof(f268,plain,(
% 0.19/0.44    spl2_28 <=> ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.19/0.44  fof(f297,plain,(
% 0.19/0.44    spl2_32 <=> ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.19/0.44  fof(f772,plain,(
% 0.19/0.44    spl2_88 <=> r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1)))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 0.19/0.44  fof(f870,plain,(
% 0.19/0.44    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl2_28 | ~spl2_32 | ~spl2_88)),
% 0.19/0.44    inference(forward_demodulation,[],[f869,f269])).
% 0.19/0.44  fof(f269,plain,(
% 0.19/0.44    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0)) ) | ~spl2_28),
% 0.19/0.44    inference(avatar_component_clause,[],[f268])).
% 0.19/0.44  fof(f869,plain,(
% 0.19/0.44    sK0 = k10_relat_1(sK1,k10_relat_1(k2_funct_1(sK1),sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl2_32 | ~spl2_88)),
% 0.19/0.44    inference(forward_demodulation,[],[f823,f298])).
% 0.19/0.44  fof(f298,plain,(
% 0.19/0.44    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0)) ) | ~spl2_32),
% 0.19/0.44    inference(avatar_component_clause,[],[f297])).
% 0.19/0.44  fof(f823,plain,(
% 0.19/0.44    sK0 = k9_relat_1(k2_funct_1(sK1),k10_relat_1(k2_funct_1(sK1),sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl2_88),
% 0.19/0.44    inference(resolution,[],[f774,f65])).
% 0.19/0.44  fof(f65,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f36])).
% 0.19/0.44  fof(f36,plain,(
% 0.19/0.44    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.44    inference(flattening,[],[f35])).
% 0.19/0.44  fof(f35,plain,(
% 0.19/0.44    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.44    inference(ennf_transformation,[],[f14])).
% 0.19/0.44  fof(f14,axiom,(
% 0.19/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.19/0.44  fof(f774,plain,(
% 0.19/0.44    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1))) | ~spl2_88),
% 0.19/0.44    inference(avatar_component_clause,[],[f772])).
% 0.19/0.44  fof(f775,plain,(
% 0.19/0.44    spl2_88 | ~spl2_61 | ~spl2_69),
% 0.19/0.44    inference(avatar_split_clause,[],[f766,f624,f560,f772])).
% 0.19/0.44  fof(f560,plain,(
% 0.19/0.44    spl2_61 <=> r1_tarski(sK0,k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 0.19/0.44  fof(f624,plain,(
% 0.19/0.44    spl2_69 <=> k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 0.19/0.44  fof(f766,plain,(
% 0.19/0.44    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1))) | (~spl2_61 | ~spl2_69)),
% 0.19/0.44    inference(backward_demodulation,[],[f562,f626])).
% 0.19/0.44  fof(f626,plain,(
% 0.19/0.44    k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) | ~spl2_69),
% 0.19/0.44    inference(avatar_component_clause,[],[f624])).
% 0.19/0.44  fof(f562,plain,(
% 0.19/0.44    r1_tarski(sK0,k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))) | ~spl2_61),
% 0.19/0.44    inference(avatar_component_clause,[],[f560])).
% 0.19/0.44  fof(f627,plain,(
% 0.19/0.44    ~spl2_5 | spl2_69 | ~spl2_4 | ~spl2_32),
% 0.19/0.44    inference(avatar_split_clause,[],[f622,f297,f92,f624,f97])).
% 0.19/0.44  fof(f97,plain,(
% 0.19/0.44    spl2_5 <=> v1_relat_1(sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.44  fof(f92,plain,(
% 0.19/0.44    spl2_4 <=> v1_funct_1(sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.44  fof(f622,plain,(
% 0.19/0.44    k2_relat_1(k2_funct_1(sK1)) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(sK1) | (~spl2_4 | ~spl2_32)),
% 0.19/0.44    inference(forward_demodulation,[],[f605,f298])).
% 0.19/0.44  fof(f605,plain,(
% 0.19/0.44    k2_relat_1(k2_funct_1(sK1)) = k9_relat_1(k2_funct_1(sK1),k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(sK1) | ~spl2_4),
% 0.19/0.44    inference(resolution,[],[f146,f94])).
% 0.19/0.44  fof(f94,plain,(
% 0.19/0.44    v1_funct_1(sK1) | ~spl2_4),
% 0.19/0.44    inference(avatar_component_clause,[],[f92])).
% 0.19/0.44  fof(f146,plain,(
% 0.19/0.44    ( ! [X0] : (~v1_funct_1(X0) | k2_relat_1(k2_funct_1(X0)) = k9_relat_1(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0))) | ~v1_relat_1(X0)) )),
% 0.19/0.44    inference(resolution,[],[f54,f55])).
% 0.19/0.44  fof(f55,plain,(
% 0.19/0.44    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f26])).
% 0.19/0.44  fof(f26,plain,(
% 0.19/0.44    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(flattening,[],[f25])).
% 0.19/0.44  fof(f25,plain,(
% 0.19/0.44    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f13])).
% 0.19/0.44  fof(f13,axiom,(
% 0.19/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.19/0.44  fof(f54,plain,(
% 0.19/0.44    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f24])).
% 0.19/0.44  fof(f24,plain,(
% 0.19/0.44    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f9])).
% 0.19/0.44  fof(f9,axiom,(
% 0.19/0.44    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.19/0.44  fof(f598,plain,(
% 0.19/0.44    spl2_61 | ~spl2_3 | ~spl2_47),
% 0.19/0.44    inference(avatar_split_clause,[],[f557,f396,f87,f560])).
% 0.19/0.44  fof(f87,plain,(
% 0.19/0.44    spl2_3 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.44  fof(f396,plain,(
% 0.19/0.44    spl2_47 <=> r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.19/0.44  fof(f557,plain,(
% 0.19/0.44    r1_tarski(sK0,k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))) | (~spl2_3 | ~spl2_47)),
% 0.19/0.44    inference(resolution,[],[f398,f176])).
% 0.19/0.44  fof(f176,plain,(
% 0.19/0.44    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | r1_tarski(sK0,X0)) ) | ~spl2_3),
% 0.19/0.44    inference(resolution,[],[f70,f89])).
% 0.19/0.44  fof(f89,plain,(
% 0.19/0.44    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_3),
% 0.19/0.44    inference(avatar_component_clause,[],[f87])).
% 0.19/0.44  fof(f70,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f42])).
% 0.19/0.44  fof(f42,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.44    inference(flattening,[],[f41])).
% 0.19/0.44  fof(f41,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.44    inference(ennf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.44  fof(f398,plain,(
% 0.19/0.44    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))) | ~spl2_47),
% 0.19/0.44    inference(avatar_component_clause,[],[f396])).
% 0.19/0.44  fof(f399,plain,(
% 0.19/0.44    spl2_47 | ~spl2_5 | ~spl2_9 | ~spl2_42),
% 0.19/0.44    inference(avatar_split_clause,[],[f394,f363,f125,f97,f396])).
% 0.19/0.44  fof(f125,plain,(
% 0.19/0.44    spl2_9 <=> k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.19/0.44  fof(f363,plain,(
% 0.19/0.44    spl2_42 <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1)))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.19/0.44  fof(f394,plain,(
% 0.19/0.44    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))) | (~spl2_5 | ~spl2_9 | ~spl2_42)),
% 0.19/0.44    inference(forward_demodulation,[],[f367,f127])).
% 0.19/0.44  fof(f127,plain,(
% 0.19/0.44    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~spl2_9),
% 0.19/0.44    inference(avatar_component_clause,[],[f125])).
% 0.19/0.44  fof(f367,plain,(
% 0.19/0.44    r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))) | (~spl2_5 | ~spl2_42)),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f99,f365,f67])).
% 0.19/0.44  fof(f67,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f38])).
% 0.19/0.44  fof(f38,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.19/0.44    inference(flattening,[],[f37])).
% 0.19/0.44  fof(f37,plain,(
% 0.19/0.44    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.44    inference(ennf_transformation,[],[f11])).
% 0.19/0.44  fof(f11,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.19/0.44  fof(f365,plain,(
% 0.19/0.44    r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) | ~spl2_42),
% 0.19/0.44    inference(avatar_component_clause,[],[f363])).
% 0.19/0.44  fof(f99,plain,(
% 0.19/0.44    v1_relat_1(sK1) | ~spl2_5),
% 0.19/0.44    inference(avatar_component_clause,[],[f97])).
% 0.19/0.44  fof(f366,plain,(
% 0.19/0.44    ~spl2_6 | ~spl2_7 | ~spl2_5 | ~spl2_4 | spl2_42 | ~spl2_24),
% 0.19/0.44    inference(avatar_split_clause,[],[f361,f234,f363,f92,f97,f109,f103])).
% 0.19/0.44  fof(f234,plain,(
% 0.19/0.44    spl2_24 <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.19/0.44  fof(f361,plain,(
% 0.19/0.44    r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl2_24),
% 0.19/0.44    inference(trivial_inequality_removal,[],[f360])).
% 0.19/0.44  fof(f360,plain,(
% 0.19/0.44    k1_relat_1(sK1) != k1_relat_1(sK1) | r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl2_24),
% 0.19/0.44    inference(forward_demodulation,[],[f359,f51])).
% 0.19/0.44  fof(f51,plain,(
% 0.19/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.44    inference(cnf_transformation,[],[f12])).
% 0.19/0.44  fof(f12,axiom,(
% 0.19/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.44  fof(f359,plain,(
% 0.19/0.44    k1_relat_1(sK1) != k1_relat_1(k6_relat_1(k1_relat_1(sK1))) | r1_tarski(k2_relat_1(sK1),k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl2_24),
% 0.19/0.44    inference(superposition,[],[f59,f236])).
% 0.19/0.44  fof(f236,plain,(
% 0.19/0.44    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~spl2_24),
% 0.19/0.44    inference(avatar_component_clause,[],[f234])).
% 0.19/0.44  fof(f59,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f30])).
% 0.19/0.44  fof(f30,plain,(
% 0.19/0.44    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(flattening,[],[f29])).
% 0.19/0.44  fof(f29,plain,(
% 0.19/0.44    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(k5_relat_1(X1,X0)) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f17])).
% 0.19/0.44  fof(f17,axiom,(
% 0.19/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 0.19/0.44  fof(f299,plain,(
% 0.19/0.44    ~spl2_5 | ~spl2_4 | spl2_32 | ~spl2_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f295,f82,f297,f92,f97])).
% 0.19/0.44  fof(f82,plain,(
% 0.19/0.44    spl2_2 <=> v2_funct_1(sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.44  fof(f295,plain,(
% 0.19/0.44    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k2_funct_1(sK1),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl2_2),
% 0.19/0.44    inference(resolution,[],[f64,f84])).
% 0.19/0.44  fof(f84,plain,(
% 0.19/0.44    v2_funct_1(sK1) | ~spl2_2),
% 0.19/0.44    inference(avatar_component_clause,[],[f82])).
% 0.19/0.44  fof(f64,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f34])).
% 0.19/0.44  fof(f34,plain,(
% 0.19/0.44    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.44    inference(flattening,[],[f33])).
% 0.19/0.44  fof(f33,plain,(
% 0.19/0.44    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.44    inference(ennf_transformation,[],[f16])).
% 0.19/0.44  fof(f16,axiom,(
% 0.19/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 0.19/0.44  fof(f270,plain,(
% 0.19/0.44    ~spl2_5 | ~spl2_4 | spl2_28 | ~spl2_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f266,f82,f268,f92,f97])).
% 0.19/0.44  fof(f266,plain,(
% 0.19/0.44    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k2_funct_1(sK1),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl2_2),
% 0.19/0.44    inference(resolution,[],[f63,f84])).
% 0.19/0.44  fof(f63,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f32])).
% 0.19/0.44  fof(f32,plain,(
% 0.19/0.44    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.44    inference(flattening,[],[f31])).
% 0.19/0.44  fof(f31,plain,(
% 0.19/0.44    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.44    inference(ennf_transformation,[],[f15])).
% 0.19/0.44  fof(f15,axiom,(
% 0.19/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.19/0.44  fof(f238,plain,(
% 0.19/0.44    ~spl2_5 | ~spl2_4 | spl2_24 | ~spl2_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f232,f82,f234,f92,f97])).
% 0.19/0.44  fof(f232,plain,(
% 0.19/0.44    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl2_2),
% 0.19/0.44    inference(resolution,[],[f57,f84])).
% 0.19/0.44  fof(f57,plain,(
% 0.19/0.44    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f28])).
% 0.19/0.44  fof(f28,plain,(
% 0.19/0.44    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(flattening,[],[f27])).
% 0.19/0.44  fof(f27,plain,(
% 0.19/0.44    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f18])).
% 0.19/0.44  fof(f18,axiom,(
% 0.19/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.19/0.44  fof(f129,plain,(
% 0.19/0.44    spl2_9 | ~spl2_5),
% 0.19/0.44    inference(avatar_split_clause,[],[f116,f97,f125])).
% 0.19/0.44  fof(f116,plain,(
% 0.19/0.44    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~spl2_5),
% 0.19/0.44    inference(resolution,[],[f53,f99])).
% 0.19/0.44  fof(f53,plain,(
% 0.19/0.44    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f23])).
% 0.19/0.44  fof(f23,plain,(
% 0.19/0.44    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f10])).
% 0.19/0.44  fof(f10,axiom,(
% 0.19/0.44    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.19/0.44  fof(f112,plain,(
% 0.19/0.44    spl2_7 | ~spl2_4 | ~spl2_5),
% 0.19/0.44    inference(avatar_split_clause,[],[f107,f97,f92,f109])).
% 0.19/0.44  fof(f107,plain,(
% 0.19/0.44    v1_funct_1(k2_funct_1(sK1)) | (~spl2_4 | ~spl2_5)),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f99,f94,f56])).
% 0.19/0.44  fof(f56,plain,(
% 0.19/0.44    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f26])).
% 0.19/0.44  fof(f106,plain,(
% 0.19/0.44    spl2_6 | ~spl2_4 | ~spl2_5),
% 0.19/0.44    inference(avatar_split_clause,[],[f101,f97,f92,f103])).
% 0.19/0.44  fof(f101,plain,(
% 0.19/0.44    v1_relat_1(k2_funct_1(sK1)) | (~spl2_4 | ~spl2_5)),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f99,f94,f55])).
% 0.19/0.44  fof(f100,plain,(
% 0.19/0.44    spl2_5),
% 0.19/0.44    inference(avatar_split_clause,[],[f45,f97])).
% 0.19/0.44  fof(f45,plain,(
% 0.19/0.44    v1_relat_1(sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f44])).
% 0.19/0.44  fof(f44,plain,(
% 0.19/0.44    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f43])).
% 0.19/0.44  fof(f43,plain,(
% 0.19/0.44    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.19/0.44    inference(flattening,[],[f21])).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.19/0.44    inference(ennf_transformation,[],[f20])).
% 0.19/0.44  fof(f20,negated_conjecture,(
% 0.19/0.44    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.19/0.44    inference(negated_conjecture,[],[f19])).
% 0.19/0.44  fof(f19,conjecture,(
% 0.19/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.19/0.44  fof(f95,plain,(
% 0.19/0.44    spl2_4),
% 0.19/0.44    inference(avatar_split_clause,[],[f46,f92])).
% 0.19/0.44  fof(f46,plain,(
% 0.19/0.44    v1_funct_1(sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f44])).
% 0.19/0.44  fof(f90,plain,(
% 0.19/0.44    spl2_3),
% 0.19/0.44    inference(avatar_split_clause,[],[f47,f87])).
% 0.19/0.44  fof(f47,plain,(
% 0.19/0.44    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.19/0.44    inference(cnf_transformation,[],[f44])).
% 0.19/0.44  fof(f85,plain,(
% 0.19/0.44    spl2_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f48,f82])).
% 0.19/0.44  fof(f48,plain,(
% 0.19/0.44    v2_funct_1(sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f44])).
% 0.19/0.44  fof(f80,plain,(
% 0.19/0.44    ~spl2_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f49,f77])).
% 0.19/0.44  fof(f49,plain,(
% 0.19/0.44    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.19/0.44    inference(cnf_transformation,[],[f44])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (1928)------------------------------
% 0.19/0.44  % (1928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (1928)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (1928)Memory used [KB]: 6780
% 0.19/0.44  % (1928)Time elapsed: 0.041 s
% 0.19/0.44  % (1928)------------------------------
% 0.19/0.44  % (1928)------------------------------
% 0.19/0.44  % (1921)Success in time 0.089 s
%------------------------------------------------------------------------------
