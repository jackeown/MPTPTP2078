%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:08 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 297 expanded)
%              Number of leaves         :   37 ( 139 expanded)
%              Depth                    :    8
%              Number of atoms          :  532 ( 964 expanded)
%              Number of equality atoms :   65 ( 135 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1004,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f123,f248,f257,f296,f346,f352,f383,f417,f424,f444,f605,f606,f608,f640,f702,f740,f954,f971,f977,f978])).

fof(f978,plain,
    ( ~ spl6_1
    | ~ spl6_47
    | ~ spl6_7
    | ~ spl6_46
    | ~ spl6_70
    | ~ spl6_97 ),
    inference(avatar_split_clause,[],[f973,f952,f637,f441,f121,f457,f75])).

fof(f75,plain,
    ( spl6_1
  <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f457,plain,
    ( spl6_47
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f121,plain,
    ( spl6_7
  <=> ! [X0] : k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f441,plain,
    ( spl6_46
  <=> k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f637,plain,
    ( spl6_70
  <=> k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f952,plain,
    ( spl6_97
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k3_relat_1(k2_wellord1(sK2,X3)))
        | ~ r4_wellord1(k2_wellord1(sK2,X3),k2_wellord1(k2_wellord1(sK2,X3),k1_wellord1(k2_wellord1(sK2,X3),X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f973,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ spl6_7
    | ~ spl6_46
    | ~ spl6_70
    | ~ spl6_97 ),
    inference(forward_demodulation,[],[f972,f122])).

fof(f122,plain,
    ( ! [X0] : k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f972,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))))
    | ~ spl6_46
    | ~ spl6_70
    | ~ spl6_97 ),
    inference(forward_demodulation,[],[f964,f639])).

fof(f639,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f637])).

fof(f964,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))))
    | ~ spl6_46
    | ~ spl6_97 ),
    inference(superposition,[],[f953,f443])).

fof(f443,plain,
    ( k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f441])).

fof(f953,plain,
    ( ! [X2,X3] :
        ( ~ r4_wellord1(k2_wellord1(sK2,X3),k2_wellord1(k2_wellord1(sK2,X3),k1_wellord1(k2_wellord1(sK2,X3),X2)))
        | ~ r2_hidden(X2,k3_relat_1(k2_wellord1(sK2,X3))) )
    | ~ spl6_97 ),
    inference(avatar_component_clause,[],[f952])).

fof(f977,plain,
    ( ~ spl6_79
    | ~ spl6_1
    | ~ spl6_62
    | spl6_98 ),
    inference(avatar_split_clause,[],[f975,f968,f569,f75,f730])).

fof(f730,plain,
    ( spl6_79
  <=> v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f569,plain,
    ( spl6_62
  <=> v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f968,plain,
    ( spl6_98
  <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k2_wellord1(sK2,k1_wellord1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f975,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | spl6_98 ),
    inference(resolution,[],[f970,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f970,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | spl6_98 ),
    inference(avatar_component_clause,[],[f968])).

fof(f971,plain,
    ( ~ spl6_98
    | ~ spl6_32
    | ~ spl6_7
    | ~ spl6_31
    | ~ spl6_43
    | ~ spl6_97 ),
    inference(avatar_split_clause,[],[f966,f952,f421,f339,f121,f343,f968])).

fof(f343,plain,
    ( spl6_32
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f339,plain,
    ( spl6_31
  <=> k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f421,plain,
    ( spl6_43
  <=> k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f966,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ spl6_7
    | ~ spl6_31
    | ~ spl6_43
    | ~ spl6_97 ),
    inference(forward_demodulation,[],[f965,f122])).

fof(f965,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))))
    | ~ spl6_31
    | ~ spl6_43
    | ~ spl6_97 ),
    inference(forward_demodulation,[],[f963,f341])).

fof(f341,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f339])).

fof(f963,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)))
    | ~ r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))))
    | ~ spl6_43
    | ~ spl6_97 ),
    inference(superposition,[],[f953,f423])).

fof(f423,plain,
    ( k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f421])).

fof(f954,plain,
    ( ~ spl6_6
    | spl6_97
    | ~ spl6_77 ),
    inference(avatar_split_clause,[],[f948,f700,f952,f100])).

fof(f100,plain,
    ( spl6_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f700,plain,
    ( spl6_77
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(sK2,X1)))
        | ~ v1_relat_1(k2_wellord1(sK2,X1))
        | ~ r4_wellord1(k2_wellord1(sK2,X1),k2_wellord1(k2_wellord1(sK2,X1),k1_wellord1(k2_wellord1(sK2,X1),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f948,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k3_relat_1(k2_wellord1(sK2,X3)))
        | ~ r4_wellord1(k2_wellord1(sK2,X3),k2_wellord1(k2_wellord1(sK2,X3),k1_wellord1(k2_wellord1(sK2,X3),X2)))
        | ~ v1_relat_1(sK2) )
    | ~ spl6_77 ),
    inference(resolution,[],[f701,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f701,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k2_wellord1(sK2,X1))
        | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(sK2,X1)))
        | ~ r4_wellord1(k2_wellord1(sK2,X1),k2_wellord1(k2_wellord1(sK2,X1),k1_wellord1(k2_wellord1(sK2,X1),X0))) )
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f700])).

fof(f740,plain,
    ( ~ spl6_6
    | spl6_79 ),
    inference(avatar_split_clause,[],[f738,f730,f100])).

fof(f738,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_79 ),
    inference(resolution,[],[f732,f60])).

fof(f732,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | spl6_79 ),
    inference(avatar_component_clause,[],[f730])).

fof(f702,plain,
    ( ~ spl6_6
    | spl6_77
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f696,f95,f700,f100])).

fof(f95,plain,
    ( spl6_5
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f696,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(sK2,X1)))
        | ~ r4_wellord1(k2_wellord1(sK2,X1),k2_wellord1(k2_wellord1(sK2,X1),k1_wellord1(k2_wellord1(sK2,X1),X0)))
        | ~ v1_relat_1(k2_wellord1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f129,f97])).

fof(f97,plain,
    ( v2_wellord1(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f129,plain,(
    ! [X2,X3,X1] :
      ( ~ v2_wellord1(X1)
      | ~ r2_hidden(X3,k3_relat_1(k2_wellord1(X1,X2)))
      | ~ r4_wellord1(k2_wellord1(X1,X2),k2_wellord1(k2_wellord1(X1,X2),k1_wellord1(k2_wellord1(X1,X2),X3)))
      | ~ v1_relat_1(k2_wellord1(X1,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f40,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(f640,plain,
    ( spl6_70
    | ~ spl6_6
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f635,f506,f100,f637])).

fof(f506,plain,
    ( spl6_54
  <=> r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f635,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))
    | ~ spl6_6
    | ~ spl6_54 ),
    inference(resolution,[],[f507,f126])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_wellord1(sK2,X0) = k2_wellord1(k2_wellord1(sK2,X1),X0) )
    | ~ spl6_6 ),
    inference(resolution,[],[f63,f102])).

fof(f102,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f507,plain,
    ( r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f506])).

fof(f608,plain,
    ( ~ spl6_6
    | ~ spl6_47
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_5
    | spl6_54 ),
    inference(avatar_split_clause,[],[f539,f506,f95,f85,f90,f457,f100])).

fof(f90,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f85,plain,
    ( spl6_3
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f539,plain,
    ( ~ v2_wellord1(sK2)
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | spl6_54 ),
    inference(resolution,[],[f508,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
            | X0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).

fof(f508,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | spl6_54 ),
    inference(avatar_component_clause,[],[f506])).

fof(f606,plain,
    ( ~ spl6_6
    | ~ spl6_36
    | spl6_2
    | spl6_47 ),
    inference(avatar_split_clause,[],[f461,f457,f80,f380,f100])).

fof(f380,plain,
    ( spl6_36
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f80,plain,
    ( spl6_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f461,plain,
    ( sK0 = sK1
    | ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ v1_relat_1(sK2)
    | spl6_47 ),
    inference(resolution,[],[f459,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_wellord1(X0,X1))
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f459,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | spl6_47 ),
    inference(avatar_component_clause,[],[f457])).

fof(f605,plain,
    ( ~ spl6_6
    | spl6_62 ),
    inference(avatar_split_clause,[],[f603,f569,f100])).

fof(f603,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_62 ),
    inference(resolution,[],[f571,f60])).

fof(f571,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | spl6_62 ),
    inference(avatar_component_clause,[],[f569])).

fof(f444,plain,
    ( spl6_2
    | spl6_46
    | ~ spl6_23
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f434,f380,f255,f441,f80])).

fof(f255,plain,
    ( spl6_23
  <=> ! [X3,X2] :
        ( k1_wellord1(sK2,X2) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X3)),X2)
        | ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | X2 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f434,plain,
    ( k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1)
    | sK0 = sK1
    | ~ spl6_23
    | ~ spl6_36 ),
    inference(resolution,[],[f382,f256])).

fof(f256,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | k1_wellord1(sK2,X2) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X3)),X2)
        | X2 = X3 )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f255])).

fof(f382,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f380])).

fof(f424,plain,
    ( spl6_43
    | ~ spl6_22
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f418,f343,f246,f421])).

fof(f246,plain,
    ( spl6_22
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f418,plain,
    ( k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)
    | ~ spl6_22
    | ~ spl6_32 ),
    inference(resolution,[],[f344,f247])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f246])).

fof(f344,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f343])).

fof(f417,plain,
    ( ~ spl6_5
    | ~ spl6_6
    | spl6_14 ),
    inference(avatar_split_clause,[],[f405,f172,f100,f95])).

fof(f172,plain,
    ( spl6_14
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f405,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_wellord1(sK2)
    | spl6_14 ),
    inference(resolution,[],[f173,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f173,plain,
    ( ~ v6_relat_2(sK2)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f383,plain,
    ( ~ spl6_14
    | ~ spl6_6
    | spl6_36
    | spl6_2
    | ~ spl6_4
    | ~ spl6_3
    | spl6_33 ),
    inference(avatar_split_clause,[],[f356,f349,f85,f90,f80,f380,f100,f172])).

fof(f349,plain,
    ( spl6_33
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f356,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | sK0 = sK1
    | r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v6_relat_2(sK2)
    | spl6_33 ),
    inference(resolution,[],[f41,f351])).

fof(f351,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl6_33 ),
    inference(avatar_component_clause,[],[f349])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,X1),X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f352,plain,
    ( ~ spl6_6
    | ~ spl6_33
    | spl6_2
    | spl6_32 ),
    inference(avatar_split_clause,[],[f347,f343,f80,f349,f100])).

fof(f347,plain,
    ( sK0 = sK1
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v1_relat_1(sK2)
    | spl6_32 ),
    inference(resolution,[],[f345,f68])).

fof(f345,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | spl6_32 ),
    inference(avatar_component_clause,[],[f343])).

fof(f346,plain,
    ( spl6_31
    | ~ spl6_32
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f331,f294,f90,f85,f343,f339])).

fof(f294,plain,
    ( spl6_26
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | k2_wellord1(sK2,k1_wellord1(sK2,X0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),k1_wellord1(sK2,X0))
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ r2_hidden(X1,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f331,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_26 ),
    inference(resolution,[],[f297,f92])).

fof(f92,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k1_wellord1(sK2,sK1))
        | k2_wellord1(sK2,k1_wellord1(sK2,X0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,X0)) )
    | ~ spl6_3
    | ~ spl6_26 ),
    inference(resolution,[],[f295,f87])).

fof(f87,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | k2_wellord1(sK2,k1_wellord1(sK2,X0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),k1_wellord1(sK2,X0)) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f294])).

fof(f296,plain,
    ( ~ spl6_6
    | spl6_26
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f291,f100,f95,f294,f100])).

fof(f291,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ v1_relat_1(sK2)
        | k2_wellord1(sK2,k1_wellord1(sK2,X0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),k1_wellord1(sK2,X0)) )
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(resolution,[],[f290,f97])).

fof(f290,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_wellord1(X0)
        | ~ r2_hidden(X1,k3_relat_1(X0))
        | ~ r2_hidden(X2,k3_relat_1(X0))
        | ~ r2_hidden(X1,k1_wellord1(X0,X2))
        | ~ v1_relat_1(X0)
        | k2_wellord1(sK2,k1_wellord1(X0,X1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(X0,X2)),k1_wellord1(X0,X1)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f66,f126])).

fof(f257,plain,
    ( ~ spl6_6
    | spl6_23
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f251,f246,f255,f100])).

fof(f251,plain,
    ( ! [X2,X3] :
        ( k1_wellord1(sK2,X2) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X3)),X2)
        | X2 = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_22 ),
    inference(resolution,[],[f247,f68])).

fof(f248,plain,
    ( spl6_22
    | ~ spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f243,f95,f100,f246])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f67,f97])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X0,k1_wellord1(X2,X1))
          & v2_wellord1(X2) )
       => k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_wellord1)).

fof(f123,plain,
    ( spl6_7
    | ~ spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f118,f95,f100,f121])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0))) )
    | ~ spl6_5 ),
    inference(resolution,[],[f62,f97])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

fof(f103,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f34,f100])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
      & X0 != X1
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
      & X0 != X1
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
            & X0 != X1
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
          & X0 != X1
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_wellord1)).

fof(f98,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f35,f95])).

fof(f35,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f36,f90])).

fof(f36,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f38,f80])).

fof(f38,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:51:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.50  % (30905)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (30906)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (30917)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (30908)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (30896)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (30898)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (30901)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (30900)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.17/0.52  % (30909)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.17/0.52  % (30914)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.17/0.53  % (30902)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.17/0.53  % (30904)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.17/0.53  % (30918)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.17/0.53  % (30899)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.17/0.53  % (30907)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.17/0.54  % (30893)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.17/0.54  % (30913)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.32/0.54  % (30910)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.32/0.54  % (30897)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.32/0.54  % (30894)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.54  % (30916)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.32/0.54  % (30895)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.32/0.55  % (30894)Refutation not found, incomplete strategy% (30894)------------------------------
% 1.32/0.55  % (30894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (30894)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (30894)Memory used [KB]: 10746
% 1.32/0.55  % (30894)Time elapsed: 0.127 s
% 1.32/0.55  % (30894)------------------------------
% 1.32/0.55  % (30894)------------------------------
% 1.32/0.55  % (30915)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.32/0.55  % (30911)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.32/0.56  % (30903)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.32/0.57  % (30912)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.32/0.59  % (30908)Refutation found. Thanks to Tanya!
% 1.32/0.59  % SZS status Theorem for theBenchmark
% 1.32/0.59  % SZS output start Proof for theBenchmark
% 1.32/0.59  fof(f1004,plain,(
% 1.32/0.59    $false),
% 1.32/0.59    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f123,f248,f257,f296,f346,f352,f383,f417,f424,f444,f605,f606,f608,f640,f702,f740,f954,f971,f977,f978])).
% 1.32/0.59  fof(f978,plain,(
% 1.32/0.59    ~spl6_1 | ~spl6_47 | ~spl6_7 | ~spl6_46 | ~spl6_70 | ~spl6_97),
% 1.32/0.59    inference(avatar_split_clause,[],[f973,f952,f637,f441,f121,f457,f75])).
% 1.32/0.59  fof(f75,plain,(
% 1.32/0.59    spl6_1 <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.32/0.59  fof(f457,plain,(
% 1.32/0.59    spl6_47 <=> r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 1.32/0.59  fof(f121,plain,(
% 1.32/0.59    spl6_7 <=> ! [X0] : k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.32/0.59  fof(f441,plain,(
% 1.32/0.59    spl6_46 <=> k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 1.32/0.59  fof(f637,plain,(
% 1.32/0.59    spl6_70 <=> k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 1.32/0.59  fof(f952,plain,(
% 1.32/0.59    spl6_97 <=> ! [X3,X2] : (~r2_hidden(X2,k3_relat_1(k2_wellord1(sK2,X3))) | ~r4_wellord1(k2_wellord1(sK2,X3),k2_wellord1(k2_wellord1(sK2,X3),k1_wellord1(k2_wellord1(sK2,X3),X2))))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).
% 1.32/0.59  fof(f973,plain,(
% 1.32/0.59    ~r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | (~spl6_7 | ~spl6_46 | ~spl6_70 | ~spl6_97)),
% 1.32/0.59    inference(forward_demodulation,[],[f972,f122])).
% 1.32/0.59  fof(f122,plain,(
% 1.32/0.59    ( ! [X0] : (k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))) ) | ~spl6_7),
% 1.32/0.59    inference(avatar_component_clause,[],[f121])).
% 1.32/0.59  fof(f972,plain,(
% 1.32/0.59    ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | ~r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))) | (~spl6_46 | ~spl6_70 | ~spl6_97)),
% 1.32/0.59    inference(forward_demodulation,[],[f964,f639])).
% 1.32/0.59  fof(f639,plain,(
% 1.32/0.59    k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)) | ~spl6_70),
% 1.32/0.59    inference(avatar_component_clause,[],[f637])).
% 1.32/0.59  fof(f964,plain,(
% 1.32/0.59    ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))) | ~r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))) | (~spl6_46 | ~spl6_97)),
% 1.32/0.59    inference(superposition,[],[f953,f443])).
% 1.32/0.59  fof(f443,plain,(
% 1.32/0.59    k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1) | ~spl6_46),
% 1.32/0.59    inference(avatar_component_clause,[],[f441])).
% 1.32/0.59  fof(f953,plain,(
% 1.32/0.59    ( ! [X2,X3] : (~r4_wellord1(k2_wellord1(sK2,X3),k2_wellord1(k2_wellord1(sK2,X3),k1_wellord1(k2_wellord1(sK2,X3),X2))) | ~r2_hidden(X2,k3_relat_1(k2_wellord1(sK2,X3)))) ) | ~spl6_97),
% 1.32/0.59    inference(avatar_component_clause,[],[f952])).
% 1.32/0.59  fof(f977,plain,(
% 1.32/0.59    ~spl6_79 | ~spl6_1 | ~spl6_62 | spl6_98),
% 1.32/0.59    inference(avatar_split_clause,[],[f975,f968,f569,f75,f730])).
% 1.32/0.59  fof(f730,plain,(
% 1.32/0.59    spl6_79 <=> v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 1.32/0.59  fof(f569,plain,(
% 1.32/0.59    spl6_62 <=> v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 1.32/0.59  fof(f968,plain,(
% 1.32/0.59    spl6_98 <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k2_wellord1(sK2,k1_wellord1(sK2,sK0)))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 1.32/0.59  fof(f975,plain,(
% 1.32/0.59    ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) | spl6_98),
% 1.32/0.59    inference(resolution,[],[f970,f53])).
% 1.32/0.59  fof(f53,plain,(
% 1.32/0.59    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f21])).
% 1.32/0.59  fof(f21,plain,(
% 1.32/0.59    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(flattening,[],[f20])).
% 1.32/0.59  fof(f20,plain,(
% 1.32/0.59    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(ennf_transformation,[],[f10])).
% 1.32/0.59  fof(f10,axiom,(
% 1.32/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).
% 1.32/0.59  fof(f970,plain,(
% 1.32/0.59    ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k2_wellord1(sK2,k1_wellord1(sK2,sK0))) | spl6_98),
% 1.32/0.59    inference(avatar_component_clause,[],[f968])).
% 1.32/0.59  fof(f971,plain,(
% 1.32/0.59    ~spl6_98 | ~spl6_32 | ~spl6_7 | ~spl6_31 | ~spl6_43 | ~spl6_97),
% 1.32/0.59    inference(avatar_split_clause,[],[f966,f952,f421,f339,f121,f343,f968])).
% 1.32/0.59  fof(f343,plain,(
% 1.32/0.59    spl6_32 <=> r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.32/0.59  fof(f339,plain,(
% 1.32/0.59    spl6_31 <=> k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.32/0.59  fof(f421,plain,(
% 1.32/0.59    spl6_43 <=> k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 1.32/0.59  fof(f966,plain,(
% 1.32/0.59    ~r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k2_wellord1(sK2,k1_wellord1(sK2,sK0))) | (~spl6_7 | ~spl6_31 | ~spl6_43 | ~spl6_97)),
% 1.32/0.59    inference(forward_demodulation,[],[f965,f122])).
% 1.32/0.59  fof(f965,plain,(
% 1.32/0.59    ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k2_wellord1(sK2,k1_wellord1(sK2,sK0))) | ~r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))) | (~spl6_31 | ~spl6_43 | ~spl6_97)),
% 1.32/0.59    inference(forward_demodulation,[],[f963,f341])).
% 1.32/0.59  fof(f341,plain,(
% 1.32/0.59    k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) | ~spl6_31),
% 1.32/0.59    inference(avatar_component_clause,[],[f339])).
% 1.32/0.59  fof(f963,plain,(
% 1.32/0.59    ~r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))) | ~r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))) | (~spl6_43 | ~spl6_97)),
% 1.32/0.59    inference(superposition,[],[f953,f423])).
% 1.32/0.59  fof(f423,plain,(
% 1.32/0.59    k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0) | ~spl6_43),
% 1.32/0.59    inference(avatar_component_clause,[],[f421])).
% 1.32/0.59  fof(f954,plain,(
% 1.32/0.59    ~spl6_6 | spl6_97 | ~spl6_77),
% 1.32/0.59    inference(avatar_split_clause,[],[f948,f700,f952,f100])).
% 1.32/0.59  fof(f100,plain,(
% 1.32/0.59    spl6_6 <=> v1_relat_1(sK2)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.32/0.59  fof(f700,plain,(
% 1.32/0.59    spl6_77 <=> ! [X1,X0] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(sK2,X1))) | ~v1_relat_1(k2_wellord1(sK2,X1)) | ~r4_wellord1(k2_wellord1(sK2,X1),k2_wellord1(k2_wellord1(sK2,X1),k1_wellord1(k2_wellord1(sK2,X1),X0))))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 1.32/0.59  fof(f948,plain,(
% 1.32/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k3_relat_1(k2_wellord1(sK2,X3))) | ~r4_wellord1(k2_wellord1(sK2,X3),k2_wellord1(k2_wellord1(sK2,X3),k1_wellord1(k2_wellord1(sK2,X3),X2))) | ~v1_relat_1(sK2)) ) | ~spl6_77),
% 1.32/0.59    inference(resolution,[],[f701,f60])).
% 1.32/0.59  fof(f60,plain,(
% 1.32/0.59    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f23])).
% 1.32/0.59  fof(f23,plain,(
% 1.32/0.59    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(ennf_transformation,[],[f3])).
% 1.32/0.59  fof(f3,axiom,(
% 1.32/0.59    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.32/0.59  fof(f701,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~v1_relat_1(k2_wellord1(sK2,X1)) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(sK2,X1))) | ~r4_wellord1(k2_wellord1(sK2,X1),k2_wellord1(k2_wellord1(sK2,X1),k1_wellord1(k2_wellord1(sK2,X1),X0)))) ) | ~spl6_77),
% 1.32/0.59    inference(avatar_component_clause,[],[f700])).
% 1.32/0.59  fof(f740,plain,(
% 1.32/0.59    ~spl6_6 | spl6_79),
% 1.32/0.59    inference(avatar_split_clause,[],[f738,f730,f100])).
% 1.32/0.59  fof(f738,plain,(
% 1.32/0.59    ~v1_relat_1(sK2) | spl6_79),
% 1.32/0.59    inference(resolution,[],[f732,f60])).
% 1.32/0.59  fof(f732,plain,(
% 1.32/0.59    ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) | spl6_79),
% 1.32/0.59    inference(avatar_component_clause,[],[f730])).
% 1.32/0.59  fof(f702,plain,(
% 1.32/0.59    ~spl6_6 | spl6_77 | ~spl6_5),
% 1.32/0.59    inference(avatar_split_clause,[],[f696,f95,f700,f100])).
% 1.32/0.59  fof(f95,plain,(
% 1.32/0.59    spl6_5 <=> v2_wellord1(sK2)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.32/0.59  fof(f696,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(sK2,X1))) | ~r4_wellord1(k2_wellord1(sK2,X1),k2_wellord1(k2_wellord1(sK2,X1),k1_wellord1(k2_wellord1(sK2,X1),X0))) | ~v1_relat_1(k2_wellord1(sK2,X1)) | ~v1_relat_1(sK2)) ) | ~spl6_5),
% 1.32/0.59    inference(resolution,[],[f129,f97])).
% 1.32/0.59  fof(f97,plain,(
% 1.32/0.59    v2_wellord1(sK2) | ~spl6_5),
% 1.32/0.59    inference(avatar_component_clause,[],[f95])).
% 1.32/0.59  fof(f129,plain,(
% 1.32/0.59    ( ! [X2,X3,X1] : (~v2_wellord1(X1) | ~r2_hidden(X3,k3_relat_1(k2_wellord1(X1,X2))) | ~r4_wellord1(k2_wellord1(X1,X2),k2_wellord1(k2_wellord1(X1,X2),k1_wellord1(k2_wellord1(X1,X2),X3))) | ~v1_relat_1(k2_wellord1(X1,X2)) | ~v1_relat_1(X1)) )),
% 1.32/0.59    inference(resolution,[],[f40,f61])).
% 1.32/0.59  fof(f61,plain,(
% 1.32/0.59    ( ! [X0,X1] : (v2_wellord1(k2_wellord1(X1,X0)) | ~v2_wellord1(X1) | ~v1_relat_1(X1)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f25])).
% 1.32/0.59  fof(f25,plain,(
% 1.32/0.59    ! [X0,X1] : (v2_wellord1(k2_wellord1(X1,X0)) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 1.32/0.59    inference(flattening,[],[f24])).
% 1.32/0.59  fof(f24,plain,(
% 1.32/0.59    ! [X0,X1] : ((v2_wellord1(k2_wellord1(X1,X0)) | ~v2_wellord1(X1)) | ~v1_relat_1(X1))),
% 1.32/0.59    inference(ennf_transformation,[],[f6])).
% 1.32/0.59  fof(f6,axiom,(
% 1.32/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => v2_wellord1(k2_wellord1(X1,X0))))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).
% 1.32/0.59  fof(f40,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~v2_wellord1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))) )),
% 1.32/0.59    inference(cnf_transformation,[],[f17])).
% 1.32/0.59  fof(f17,plain,(
% 1.32/0.59    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(flattening,[],[f16])).
% 1.32/0.59  fof(f16,plain,(
% 1.32/0.59    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(ennf_transformation,[],[f11])).
% 1.32/0.59  fof(f11,axiom,(
% 1.32/0.59    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).
% 1.32/0.59  fof(f640,plain,(
% 1.32/0.59    spl6_70 | ~spl6_6 | ~spl6_54),
% 1.32/0.59    inference(avatar_split_clause,[],[f635,f506,f100,f637])).
% 1.32/0.59  fof(f506,plain,(
% 1.32/0.59    spl6_54 <=> r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 1.32/0.59  fof(f635,plain,(
% 1.32/0.59    k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)) | (~spl6_6 | ~spl6_54)),
% 1.32/0.59    inference(resolution,[],[f507,f126])).
% 1.32/0.59  fof(f126,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_wellord1(sK2,X0) = k2_wellord1(k2_wellord1(sK2,X1),X0)) ) | ~spl6_6),
% 1.32/0.59    inference(resolution,[],[f63,f102])).
% 1.32/0.59  fof(f102,plain,(
% 1.32/0.59    v1_relat_1(sK2) | ~spl6_6),
% 1.32/0.59    inference(avatar_component_clause,[],[f100])).
% 1.32/0.59  fof(f63,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f29])).
% 1.32/0.59  fof(f29,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.32/0.59    inference(flattening,[],[f28])).
% 1.32/0.59  fof(f28,plain,(
% 1.32/0.59    ! [X0,X1,X2] : ((k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.32/0.59    inference(ennf_transformation,[],[f5])).
% 1.32/0.59  fof(f5,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).
% 1.32/0.59  fof(f507,plain,(
% 1.32/0.59    r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | ~spl6_54),
% 1.32/0.59    inference(avatar_component_clause,[],[f506])).
% 1.32/0.59  fof(f608,plain,(
% 1.32/0.59    ~spl6_6 | ~spl6_47 | ~spl6_4 | ~spl6_3 | ~spl6_5 | spl6_54),
% 1.32/0.59    inference(avatar_split_clause,[],[f539,f506,f95,f85,f90,f457,f100])).
% 1.32/0.59  fof(f90,plain,(
% 1.32/0.59    spl6_4 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.32/0.59  fof(f85,plain,(
% 1.32/0.59    spl6_3 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.32/0.59  fof(f539,plain,(
% 1.32/0.59    ~v2_wellord1(sK2) | ~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~v1_relat_1(sK2) | spl6_54),
% 1.32/0.59    inference(resolution,[],[f508,f66])).
% 1.32/0.59  fof(f66,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~v2_wellord1(X2) | ~r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f31])).
% 1.32/0.59  fof(f31,plain,(
% 1.32/0.59    ! [X0,X1,X2] : ((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 1.32/0.59    inference(flattening,[],[f30])).
% 1.32/0.59  fof(f30,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) | (~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 1.32/0.59    inference(ennf_transformation,[],[f8])).
% 1.32/0.59  fof(f8,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1))))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).
% 1.32/0.59  fof(f508,plain,(
% 1.32/0.59    ~r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | spl6_54),
% 1.32/0.59    inference(avatar_component_clause,[],[f506])).
% 1.32/0.59  fof(f606,plain,(
% 1.32/0.59    ~spl6_6 | ~spl6_36 | spl6_2 | spl6_47),
% 1.32/0.59    inference(avatar_split_clause,[],[f461,f457,f80,f380,f100])).
% 1.32/0.59  fof(f380,plain,(
% 1.32/0.59    spl6_36 <=> r2_hidden(k4_tarski(sK1,sK0),sK2)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 1.32/0.59  fof(f80,plain,(
% 1.32/0.59    spl6_2 <=> sK0 = sK1),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.32/0.59  fof(f461,plain,(
% 1.32/0.59    sK0 = sK1 | ~r2_hidden(k4_tarski(sK1,sK0),sK2) | ~v1_relat_1(sK2) | spl6_47),
% 1.32/0.59    inference(resolution,[],[f459,f68])).
% 1.32/0.59  fof(f68,plain,(
% 1.32/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_wellord1(X0,X1)) | X1 = X3 | ~r2_hidden(k4_tarski(X3,X1),X0) | ~v1_relat_1(X0)) )),
% 1.32/0.59    inference(equality_resolution,[],[f59])).
% 1.32/0.59  fof(f59,plain,(
% 1.32/0.59    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | X1 = X3 | ~r2_hidden(k4_tarski(X3,X1),X0) | r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 1.32/0.59    inference(cnf_transformation,[],[f22])).
% 1.32/0.59  fof(f22,plain,(
% 1.32/0.59    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(ennf_transformation,[],[f1])).
% 1.32/0.59  fof(f1,axiom,(
% 1.32/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 1.32/0.59  fof(f459,plain,(
% 1.32/0.59    ~r2_hidden(sK1,k1_wellord1(sK2,sK0)) | spl6_47),
% 1.32/0.59    inference(avatar_component_clause,[],[f457])).
% 1.32/0.59  fof(f605,plain,(
% 1.32/0.59    ~spl6_6 | spl6_62),
% 1.32/0.59    inference(avatar_split_clause,[],[f603,f569,f100])).
% 1.32/0.59  fof(f603,plain,(
% 1.32/0.59    ~v1_relat_1(sK2) | spl6_62),
% 1.32/0.59    inference(resolution,[],[f571,f60])).
% 1.32/0.59  fof(f571,plain,(
% 1.32/0.59    ~v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) | spl6_62),
% 1.32/0.59    inference(avatar_component_clause,[],[f569])).
% 1.32/0.59  fof(f444,plain,(
% 1.32/0.59    spl6_2 | spl6_46 | ~spl6_23 | ~spl6_36),
% 1.32/0.59    inference(avatar_split_clause,[],[f434,f380,f255,f441,f80])).
% 1.32/0.59  fof(f255,plain,(
% 1.32/0.59    spl6_23 <=> ! [X3,X2] : (k1_wellord1(sK2,X2) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X3)),X2) | ~r2_hidden(k4_tarski(X2,X3),sK2) | X2 = X3)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.32/0.59  fof(f434,plain,(
% 1.32/0.59    k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1) | sK0 = sK1 | (~spl6_23 | ~spl6_36)),
% 1.32/0.59    inference(resolution,[],[f382,f256])).
% 1.32/0.59  fof(f256,plain,(
% 1.32/0.59    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_wellord1(sK2,X2) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X3)),X2) | X2 = X3) ) | ~spl6_23),
% 1.32/0.59    inference(avatar_component_clause,[],[f255])).
% 1.32/0.59  fof(f382,plain,(
% 1.32/0.59    r2_hidden(k4_tarski(sK1,sK0),sK2) | ~spl6_36),
% 1.32/0.59    inference(avatar_component_clause,[],[f380])).
% 1.32/0.59  fof(f424,plain,(
% 1.32/0.59    spl6_43 | ~spl6_22 | ~spl6_32),
% 1.32/0.59    inference(avatar_split_clause,[],[f418,f343,f246,f421])).
% 1.32/0.59  fof(f246,plain,(
% 1.32/0.59    spl6_22 <=> ! [X1,X0] : (~r2_hidden(X0,k1_wellord1(sK2,X1)) | k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.32/0.59  fof(f418,plain,(
% 1.32/0.59    k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0) | (~spl6_22 | ~spl6_32)),
% 1.32/0.59    inference(resolution,[],[f344,f247])).
% 1.32/0.59  fof(f247,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k1_wellord1(sK2,X1)) | k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0)) ) | ~spl6_22),
% 1.32/0.59    inference(avatar_component_clause,[],[f246])).
% 1.32/0.59  fof(f344,plain,(
% 1.32/0.59    r2_hidden(sK0,k1_wellord1(sK2,sK1)) | ~spl6_32),
% 1.32/0.59    inference(avatar_component_clause,[],[f343])).
% 1.32/0.59  fof(f417,plain,(
% 1.32/0.59    ~spl6_5 | ~spl6_6 | spl6_14),
% 1.32/0.59    inference(avatar_split_clause,[],[f405,f172,f100,f95])).
% 1.32/0.59  fof(f172,plain,(
% 1.32/0.59    spl6_14 <=> v6_relat_2(sK2)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.32/0.59  fof(f405,plain,(
% 1.32/0.59    ~v1_relat_1(sK2) | ~v2_wellord1(sK2) | spl6_14),
% 1.32/0.59    inference(resolution,[],[f173,f50])).
% 1.32/0.59  fof(f50,plain,(
% 1.32/0.59    ( ! [X0] : (v6_relat_2(X0) | ~v1_relat_1(X0) | ~v2_wellord1(X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f19])).
% 1.32/0.59  fof(f19,plain,(
% 1.32/0.59    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(ennf_transformation,[],[f2])).
% 1.32/0.59  fof(f2,axiom,(
% 1.32/0.59    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 1.32/0.59  fof(f173,plain,(
% 1.32/0.59    ~v6_relat_2(sK2) | spl6_14),
% 1.32/0.59    inference(avatar_component_clause,[],[f172])).
% 1.32/0.59  fof(f383,plain,(
% 1.32/0.59    ~spl6_14 | ~spl6_6 | spl6_36 | spl6_2 | ~spl6_4 | ~spl6_3 | spl6_33),
% 1.32/0.59    inference(avatar_split_clause,[],[f356,f349,f85,f90,f80,f380,f100,f172])).
% 1.32/0.59  fof(f349,plain,(
% 1.32/0.59    spl6_33 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.32/0.59  fof(f356,plain,(
% 1.32/0.59    ~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2)) | sK0 = sK1 | r2_hidden(k4_tarski(sK1,sK0),sK2) | ~v1_relat_1(sK2) | ~v6_relat_2(sK2) | spl6_33),
% 1.32/0.59    inference(resolution,[],[f41,f351])).
% 1.32/0.59  fof(f351,plain,(
% 1.32/0.59    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | spl6_33),
% 1.32/0.59    inference(avatar_component_clause,[],[f349])).
% 1.32/0.59  fof(f41,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r2_hidden(X2,k3_relat_1(X0)) | X1 = X2 | r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0) | ~v6_relat_2(X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f18])).
% 1.32/0.59  fof(f18,plain,(
% 1.32/0.59    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(ennf_transformation,[],[f4])).
% 1.32/0.59  fof(f4,axiom,(
% 1.32/0.59    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).
% 1.32/0.59  fof(f352,plain,(
% 1.32/0.59    ~spl6_6 | ~spl6_33 | spl6_2 | spl6_32),
% 1.32/0.59    inference(avatar_split_clause,[],[f347,f343,f80,f349,f100])).
% 1.32/0.59  fof(f347,plain,(
% 1.32/0.59    sK0 = sK1 | ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~v1_relat_1(sK2) | spl6_32),
% 1.32/0.59    inference(resolution,[],[f345,f68])).
% 1.32/0.59  fof(f345,plain,(
% 1.32/0.59    ~r2_hidden(sK0,k1_wellord1(sK2,sK1)) | spl6_32),
% 1.32/0.59    inference(avatar_component_clause,[],[f343])).
% 1.32/0.59  fof(f346,plain,(
% 1.32/0.59    spl6_31 | ~spl6_32 | ~spl6_3 | ~spl6_4 | ~spl6_26),
% 1.32/0.59    inference(avatar_split_clause,[],[f331,f294,f90,f85,f343,f339])).
% 1.32/0.59  fof(f294,plain,(
% 1.32/0.59    spl6_26 <=> ! [X1,X0] : (~r2_hidden(X0,k3_relat_1(sK2)) | k2_wellord1(sK2,k1_wellord1(sK2,X0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),k1_wellord1(sK2,X0)) | ~r2_hidden(X0,k1_wellord1(sK2,X1)) | ~r2_hidden(X1,k3_relat_1(sK2)))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.32/0.59  fof(f331,plain,(
% 1.32/0.59    ~r2_hidden(sK0,k1_wellord1(sK2,sK1)) | k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) | (~spl6_3 | ~spl6_4 | ~spl6_26)),
% 1.32/0.59    inference(resolution,[],[f297,f92])).
% 1.32/0.59  fof(f92,plain,(
% 1.32/0.59    r2_hidden(sK0,k3_relat_1(sK2)) | ~spl6_4),
% 1.32/0.59    inference(avatar_component_clause,[],[f90])).
% 1.32/0.59  fof(f297,plain,(
% 1.32/0.59    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X0,k1_wellord1(sK2,sK1)) | k2_wellord1(sK2,k1_wellord1(sK2,X0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,X0))) ) | (~spl6_3 | ~spl6_26)),
% 1.32/0.59    inference(resolution,[],[f295,f87])).
% 1.32/0.59  fof(f87,plain,(
% 1.32/0.59    r2_hidden(sK1,k3_relat_1(sK2)) | ~spl6_3),
% 1.32/0.59    inference(avatar_component_clause,[],[f85])).
% 1.32/0.59  fof(f295,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X0,k1_wellord1(sK2,X1)) | k2_wellord1(sK2,k1_wellord1(sK2,X0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),k1_wellord1(sK2,X0))) ) | ~spl6_26),
% 1.32/0.59    inference(avatar_component_clause,[],[f294])).
% 1.32/0.59  fof(f296,plain,(
% 1.32/0.59    ~spl6_6 | spl6_26 | ~spl6_5 | ~spl6_6),
% 1.32/0.59    inference(avatar_split_clause,[],[f291,f100,f95,f294,f100])).
% 1.32/0.59  fof(f291,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k1_wellord1(sK2,X1)) | ~v1_relat_1(sK2) | k2_wellord1(sK2,k1_wellord1(sK2,X0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),k1_wellord1(sK2,X0))) ) | (~spl6_5 | ~spl6_6)),
% 1.32/0.59    inference(resolution,[],[f290,f97])).
% 1.32/0.59  fof(f290,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k1_wellord1(X0,X2)) | ~v1_relat_1(X0) | k2_wellord1(sK2,k1_wellord1(X0,X1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(X0,X2)),k1_wellord1(X0,X1))) ) | ~spl6_6),
% 1.32/0.59    inference(resolution,[],[f66,f126])).
% 1.32/0.59  fof(f257,plain,(
% 1.32/0.59    ~spl6_6 | spl6_23 | ~spl6_22),
% 1.32/0.59    inference(avatar_split_clause,[],[f251,f246,f255,f100])).
% 1.32/0.59  fof(f251,plain,(
% 1.32/0.59    ( ! [X2,X3] : (k1_wellord1(sK2,X2) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X3)),X2) | X2 = X3 | ~r2_hidden(k4_tarski(X2,X3),sK2) | ~v1_relat_1(sK2)) ) | ~spl6_22),
% 1.32/0.59    inference(resolution,[],[f247,f68])).
% 1.32/0.59  fof(f248,plain,(
% 1.32/0.59    spl6_22 | ~spl6_6 | ~spl6_5),
% 1.32/0.59    inference(avatar_split_clause,[],[f243,f95,f100,f246])).
% 1.32/0.59  fof(f243,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_wellord1(sK2,X1)) | k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0)) ) | ~spl6_5),
% 1.32/0.59    inference(resolution,[],[f67,f97])).
% 1.32/0.59  fof(f67,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (~v2_wellord1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f33])).
% 1.32/0.59  fof(f33,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) | ~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 1.32/0.59    inference(flattening,[],[f32])).
% 1.32/0.59  fof(f32,plain,(
% 1.32/0.59    ! [X0,X1,X2] : ((k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0) | (~r2_hidden(X0,k1_wellord1(X2,X1)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 1.32/0.59    inference(ennf_transformation,[],[f7])).
% 1.32/0.59  fof(f7,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X0,k1_wellord1(X2,X1)) & v2_wellord1(X2)) => k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) = k1_wellord1(X2,X0)))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_wellord1)).
% 1.32/0.59  fof(f123,plain,(
% 1.32/0.59    spl6_7 | ~spl6_6 | ~spl6_5),
% 1.32/0.59    inference(avatar_split_clause,[],[f118,f95,f100,f121])).
% 1.32/0.59  fof(f118,plain,(
% 1.32/0.59    ( ! [X0] : (~v1_relat_1(sK2) | k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))) ) | ~spl6_5),
% 1.32/0.59    inference(resolution,[],[f62,f97])).
% 1.32/0.59  fof(f62,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~v2_wellord1(X1) | ~v1_relat_1(X1) | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))) )),
% 1.32/0.59    inference(cnf_transformation,[],[f27])).
% 1.32/0.59  fof(f27,plain,(
% 1.32/0.59    ! [X0,X1] : (k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 1.32/0.59    inference(flattening,[],[f26])).
% 1.32/0.59  fof(f26,plain,(
% 1.32/0.59    ! [X0,X1] : ((k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1)) | ~v1_relat_1(X1))),
% 1.32/0.59    inference(ennf_transformation,[],[f9])).
% 1.32/0.59  fof(f9,axiom,(
% 1.32/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).
% 1.32/0.59  fof(f103,plain,(
% 1.32/0.59    spl6_6),
% 1.32/0.59    inference(avatar_split_clause,[],[f34,f100])).
% 1.32/0.59  fof(f34,plain,(
% 1.32/0.59    v1_relat_1(sK2)),
% 1.32/0.59    inference(cnf_transformation,[],[f15])).
% 1.32/0.59  fof(f15,plain,(
% 1.32/0.59    ? [X0,X1,X2] : (r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1))) & X0 != X1 & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 1.32/0.59    inference(flattening,[],[f14])).
% 1.32/0.59  fof(f14,plain,(
% 1.32/0.59    ? [X0,X1,X2] : ((r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1))) & X0 != X1 & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) & v1_relat_1(X2))),
% 1.32/0.59    inference(ennf_transformation,[],[f13])).
% 1.32/0.59  fof(f13,negated_conjecture,(
% 1.32/0.59    ~! [X0,X1,X2] : (v1_relat_1(X2) => ~(r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1))) & X0 != X1 & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)))),
% 1.32/0.59    inference(negated_conjecture,[],[f12])).
% 1.32/0.59  fof(f12,conjecture,(
% 1.32/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => ~(r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1))) & X0 != X1 & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)))),
% 1.32/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_wellord1)).
% 1.32/0.59  fof(f98,plain,(
% 1.32/0.59    spl6_5),
% 1.32/0.59    inference(avatar_split_clause,[],[f35,f95])).
% 1.32/0.59  fof(f35,plain,(
% 1.32/0.59    v2_wellord1(sK2)),
% 1.32/0.59    inference(cnf_transformation,[],[f15])).
% 1.32/0.59  fof(f93,plain,(
% 1.32/0.59    spl6_4),
% 1.32/0.59    inference(avatar_split_clause,[],[f36,f90])).
% 1.32/0.59  fof(f36,plain,(
% 1.32/0.59    r2_hidden(sK0,k3_relat_1(sK2))),
% 1.32/0.59    inference(cnf_transformation,[],[f15])).
% 1.32/0.59  fof(f88,plain,(
% 1.32/0.59    spl6_3),
% 1.32/0.59    inference(avatar_split_clause,[],[f37,f85])).
% 1.32/0.59  fof(f37,plain,(
% 1.32/0.59    r2_hidden(sK1,k3_relat_1(sK2))),
% 1.32/0.59    inference(cnf_transformation,[],[f15])).
% 1.32/0.59  fof(f83,plain,(
% 1.32/0.59    ~spl6_2),
% 1.32/0.59    inference(avatar_split_clause,[],[f38,f80])).
% 1.32/0.59  fof(f38,plain,(
% 1.32/0.59    sK0 != sK1),
% 1.32/0.59    inference(cnf_transformation,[],[f15])).
% 1.32/0.59  fof(f78,plain,(
% 1.32/0.59    spl6_1),
% 1.32/0.59    inference(avatar_split_clause,[],[f39,f75])).
% 1.32/0.59  fof(f39,plain,(
% 1.32/0.59    r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))),
% 1.32/0.59    inference(cnf_transformation,[],[f15])).
% 1.32/0.59  % SZS output end Proof for theBenchmark
% 1.32/0.59  % (30908)------------------------------
% 1.32/0.59  % (30908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.59  % (30908)Termination reason: Refutation
% 1.32/0.59  
% 1.32/0.59  % (30908)Memory used [KB]: 7291
% 1.32/0.59  % (30908)Time elapsed: 0.120 s
% 1.32/0.59  % (30908)------------------------------
% 1.32/0.59  % (30908)------------------------------
% 1.32/0.59  % (30892)Success in time 0.222 s
%------------------------------------------------------------------------------
