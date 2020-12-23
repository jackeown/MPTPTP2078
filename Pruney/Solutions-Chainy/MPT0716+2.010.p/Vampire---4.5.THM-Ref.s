%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:50 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 281 expanded)
%              Number of leaves         :   31 ( 122 expanded)
%              Depth                    :   11
%              Number of atoms          :  466 (1343 expanded)
%              Number of equality atoms :   31 (  52 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f75,f77,f81,f85,f89,f93,f916,f930,f964,f986,f988,f1027,f1052,f1060,f1070,f1088,f1099,f1126])).

fof(f1126,plain,
    ( ~ spl4_7
    | ~ spl4_80
    | spl4_1
    | ~ spl4_5
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f1117,f914,f83,f64,f911,f91])).

fof(f91,plain,
    ( spl4_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f911,plain,
    ( spl4_80
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f64,plain,
    ( spl4_1
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f83,plain,
    ( spl4_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f914,plain,
    ( spl4_81
  <=> sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f1117,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl4_5
    | ~ spl4_81 ),
    inference(superposition,[],[f230,f915])).

fof(f915,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f914])).

fof(f230,plain,
    ( ! [X4,X5] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(X4,X5),sK1)),k1_relat_1(k5_relat_1(X4,sK1)))
        | ~ v1_relat_1(k5_relat_1(X4,sK1))
        | ~ v1_relat_1(X4) )
    | ~ spl4_5 ),
    inference(superposition,[],[f53,f145])).

fof(f145,plain,
    ( ! [X10,X11] :
        ( k7_relat_1(k5_relat_1(X10,sK1),X11) = k5_relat_1(k7_relat_1(X10,X11),sK1)
        | ~ v1_relat_1(X10) )
    | ~ spl4_5 ),
    inference(resolution,[],[f56,f84])).

fof(f84,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f1099,plain,
    ( ~ spl4_7
    | ~ spl4_84
    | ~ spl4_5
    | spl4_81
    | ~ spl4_3
    | ~ spl4_90 ),
    inference(avatar_split_clause,[],[f1098,f962,f70,f914,f83,f941,f91])).

fof(f941,plain,
    ( spl4_84
  <=> v1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f70,plain,
    ( spl4_3
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f962,plain,
    ( spl4_90
  <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f1098,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | ~ spl4_3
    | ~ spl4_90 ),
    inference(forward_demodulation,[],[f1097,f1028])).

fof(f1028,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl4_90 ),
    inference(avatar_component_clause,[],[f962])).

fof(f1097,plain,
    ( k1_relat_1(k7_relat_1(sK0,sK2)) = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f74,f224])).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X0,X1),k1_relat_1(X2))
      | k1_relat_1(k7_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(k7_relat_1(X0,X1),X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f50,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f74,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f1088,plain,
    ( ~ spl4_7
    | ~ spl4_5
    | spl4_103 ),
    inference(avatar_split_clause,[],[f1086,f1068,f83,f91])).

fof(f1068,plain,
    ( spl4_103
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).

fof(f1086,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl4_103 ),
    inference(resolution,[],[f1069,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f1069,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | spl4_103 ),
    inference(avatar_component_clause,[],[f1068])).

fof(f1070,plain,
    ( ~ spl4_103
    | ~ spl4_1
    | ~ spl4_98 ),
    inference(avatar_split_clause,[],[f1063,f1025,f64,f1068])).

fof(f1025,plain,
    ( spl4_98
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f1063,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl4_1
    | ~ spl4_98 ),
    inference(resolution,[],[f1026,f73])).

fof(f73,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f1026,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | ~ r1_tarski(X0,k1_relat_1(sK0)) )
    | ~ spl4_98 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f1060,plain,
    ( ~ spl4_7
    | spl4_3
    | ~ spl4_89 ),
    inference(avatar_split_clause,[],[f1057,f959,f70,f91])).

fof(f959,plain,
    ( spl4_89
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f1057,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl4_89 ),
    inference(superposition,[],[f960,f54])).

fof(f960,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ spl4_89 ),
    inference(avatar_component_clause,[],[f959])).

fof(f1052,plain,
    ( ~ spl4_7
    | ~ spl4_2
    | spl4_90 ),
    inference(avatar_split_clause,[],[f994,f962,f67,f91])).

fof(f67,plain,
    ( spl4_2
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f994,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl4_90 ),
    inference(trivial_inequality_removal,[],[f993])).

fof(f993,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl4_90 ),
    inference(superposition,[],[f963,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f963,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK0,sK2))
    | spl4_90 ),
    inference(avatar_component_clause,[],[f962])).

fof(f1027,plain,
    ( spl4_2
    | spl4_98
    | spl4_2 ),
    inference(avatar_split_clause,[],[f1022,f67,f1025,f67])).

fof(f1022,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,X0)
        | r1_tarski(sK2,k1_relat_1(sK0)) )
    | spl4_2 ),
    inference(resolution,[],[f999,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f999,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK2,k1_relat_1(sK0)),X1)
        | ~ r1_tarski(X0,k1_relat_1(sK0))
        | ~ r1_tarski(X1,X0) )
    | spl4_2 ),
    inference(resolution,[],[f996,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f996,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK2,k1_relat_1(sK0)),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK0)) )
    | spl4_2 ),
    inference(resolution,[],[f68,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(sK3(X0,X1),X2) ) ),
    inference(resolution,[],[f60,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f988,plain,
    ( ~ spl4_7
    | ~ spl4_6
    | spl4_88 ),
    inference(avatar_split_clause,[],[f987,f956,f87,f91])).

fof(f87,plain,
    ( spl4_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f956,plain,
    ( spl4_88
  <=> v1_funct_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f987,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl4_88 ),
    inference(resolution,[],[f957,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f957,plain,
    ( ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | spl4_88 ),
    inference(avatar_component_clause,[],[f956])).

fof(f986,plain,
    ( ~ spl4_7
    | spl4_84 ),
    inference(avatar_split_clause,[],[f985,f941,f91])).

fof(f985,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_84 ),
    inference(resolution,[],[f942,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f942,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | spl4_84 ),
    inference(avatar_component_clause,[],[f941])).

fof(f964,plain,
    ( ~ spl4_5
    | ~ spl4_4
    | ~ spl4_84
    | ~ spl4_88
    | spl4_89
    | ~ spl4_90
    | ~ spl4_81 ),
    inference(avatar_split_clause,[],[f934,f914,f962,f959,f956,f941,f79,f83])).

fof(f79,plain,
    ( spl4_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f934,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK0,sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_81 ),
    inference(superposition,[],[f51,f915])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(f930,plain,
    ( ~ spl4_7
    | ~ spl4_5
    | spl4_80 ),
    inference(avatar_split_clause,[],[f929,f911,f83,f91])).

fof(f929,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl4_80 ),
    inference(resolution,[],[f912,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f912,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl4_80 ),
    inference(avatar_component_clause,[],[f911])).

fof(f916,plain,
    ( ~ spl4_7
    | ~ spl4_80
    | spl4_81
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f892,f83,f64,f914,f911,f91])).

fof(f892,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(resolution,[],[f228,f73])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_relat_1(k5_relat_1(X0,sK1)))
        | k1_relat_1(k5_relat_1(k7_relat_1(X0,X1),sK1)) = X1
        | ~ v1_relat_1(k5_relat_1(X0,sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl4_5 ),
    inference(superposition,[],[f55,f145])).

fof(f93,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
      | ~ r1_tarski(sK2,k1_relat_1(sK0))
      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        & r1_tarski(sK2,k1_relat_1(sK0)) )
      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(sK0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
            & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(sK0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            | ~ r1_tarski(X2,k1_relat_1(sK0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
          & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
              & r1_tarski(X2,k1_relat_1(sK0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
          | ~ r1_tarski(X2,k1_relat_1(sK0))
          | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
        & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            & r1_tarski(X2,k1_relat_1(sK0)) )
          | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
   => ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
      & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
          & r1_tarski(sK2,k1_relat_1(sK0)) )
        | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(f89,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f46,f67,f64])).

fof(f46,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f47,f70,f64])).

fof(f47,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f48,f70,f67,f64])).

fof(f48,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (23508)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (23516)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (23498)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (23516)Refutation not found, incomplete strategy% (23516)------------------------------
% 0.22/0.52  % (23516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23516)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (23516)Memory used [KB]: 10746
% 0.22/0.52  % (23516)Time elapsed: 0.068 s
% 0.22/0.52  % (23516)------------------------------
% 0.22/0.52  % (23516)------------------------------
% 0.22/0.52  % (23497)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (23500)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (23499)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (23503)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (23513)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (23504)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (23521)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (23511)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (23511)Refutation not found, incomplete strategy% (23511)------------------------------
% 0.22/0.53  % (23511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23522)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (23502)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (23511)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23511)Memory used [KB]: 10618
% 0.22/0.54  % (23511)Time elapsed: 0.094 s
% 0.22/0.54  % (23511)------------------------------
% 0.22/0.54  % (23511)------------------------------
% 0.22/0.54  % (23505)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (23496)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (23514)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (23523)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (23495)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (23520)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (23515)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (23494)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (23506)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (23519)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (23507)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (23512)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (23501)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (23517)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.58  % (23509)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.59  % (23510)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.59  % (23518)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.78/0.63  % (23534)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.26/0.65  % (23513)Refutation found. Thanks to Tanya!
% 2.26/0.65  % SZS status Theorem for theBenchmark
% 2.26/0.65  % SZS output start Proof for theBenchmark
% 2.26/0.65  fof(f1127,plain,(
% 2.26/0.65    $false),
% 2.26/0.65    inference(avatar_sat_refutation,[],[f72,f75,f77,f81,f85,f89,f93,f916,f930,f964,f986,f988,f1027,f1052,f1060,f1070,f1088,f1099,f1126])).
% 2.26/0.65  fof(f1126,plain,(
% 2.26/0.65    ~spl4_7 | ~spl4_80 | spl4_1 | ~spl4_5 | ~spl4_81),
% 2.26/0.65    inference(avatar_split_clause,[],[f1117,f914,f83,f64,f911,f91])).
% 2.26/0.65  fof(f91,plain,(
% 2.26/0.65    spl4_7 <=> v1_relat_1(sK0)),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.26/0.65  fof(f911,plain,(
% 2.26/0.65    spl4_80 <=> v1_relat_1(k5_relat_1(sK0,sK1))),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 2.26/0.65  fof(f64,plain,(
% 2.26/0.65    spl4_1 <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.26/0.65  fof(f83,plain,(
% 2.26/0.65    spl4_5 <=> v1_relat_1(sK1)),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.26/0.65  fof(f914,plain,(
% 2.26/0.65    spl4_81 <=> sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 2.26/0.65  fof(f1117,plain,(
% 2.26/0.65    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0) | (~spl4_5 | ~spl4_81)),
% 2.26/0.65    inference(superposition,[],[f230,f915])).
% 2.26/0.65  fof(f915,plain,(
% 2.26/0.65    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~spl4_81),
% 2.26/0.65    inference(avatar_component_clause,[],[f914])).
% 2.26/0.65  fof(f230,plain,(
% 2.26/0.65    ( ! [X4,X5] : (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(X4,X5),sK1)),k1_relat_1(k5_relat_1(X4,sK1))) | ~v1_relat_1(k5_relat_1(X4,sK1)) | ~v1_relat_1(X4)) ) | ~spl4_5),
% 2.26/0.65    inference(superposition,[],[f53,f145])).
% 2.26/0.65  fof(f145,plain,(
% 2.26/0.65    ( ! [X10,X11] : (k7_relat_1(k5_relat_1(X10,sK1),X11) = k5_relat_1(k7_relat_1(X10,X11),sK1) | ~v1_relat_1(X10)) ) | ~spl4_5),
% 2.26/0.65    inference(resolution,[],[f56,f84])).
% 2.26/0.65  fof(f84,plain,(
% 2.26/0.65    v1_relat_1(sK1) | ~spl4_5),
% 2.26/0.65    inference(avatar_component_clause,[],[f83])).
% 2.26/0.65  fof(f56,plain,(
% 2.26/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X1)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f26])).
% 2.26/0.65  fof(f26,plain,(
% 2.26/0.65    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.26/0.65    inference(ennf_transformation,[],[f4])).
% 2.26/0.65  fof(f4,axiom,(
% 2.26/0.65    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 2.26/0.65  fof(f53,plain,(
% 2.26/0.65    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f22])).
% 2.26/0.65  fof(f22,plain,(
% 2.26/0.65    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.26/0.65    inference(ennf_transformation,[],[f8])).
% 2.26/0.65  fof(f8,axiom,(
% 2.26/0.65    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 2.26/0.65  fof(f1099,plain,(
% 2.26/0.65    ~spl4_7 | ~spl4_84 | ~spl4_5 | spl4_81 | ~spl4_3 | ~spl4_90),
% 2.26/0.65    inference(avatar_split_clause,[],[f1098,f962,f70,f914,f83,f941,f91])).
% 2.26/0.65  fof(f941,plain,(
% 2.26/0.65    spl4_84 <=> v1_relat_1(k7_relat_1(sK0,sK2))),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 2.26/0.65  fof(f70,plain,(
% 2.26/0.65    spl4_3 <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.26/0.65  fof(f962,plain,(
% 2.26/0.65    spl4_90 <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 2.26/0.65  fof(f1098,plain,(
% 2.26/0.65    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | (~spl4_3 | ~spl4_90)),
% 2.26/0.65    inference(forward_demodulation,[],[f1097,f1028])).
% 2.26/0.65  fof(f1028,plain,(
% 2.26/0.65    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) | ~spl4_90),
% 2.26/0.65    inference(avatar_component_clause,[],[f962])).
% 2.26/0.65  fof(f1097,plain,(
% 2.26/0.65    k1_relat_1(k7_relat_1(sK0,sK2)) = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | ~spl4_3),
% 2.26/0.65    inference(resolution,[],[f74,f224])).
% 2.26/0.65  fof(f224,plain,(
% 2.26/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X0,X1),k1_relat_1(X2)) | k1_relat_1(k7_relat_1(X0,X1)) = k1_relat_1(k5_relat_1(k7_relat_1(X0,X1),X2)) | ~v1_relat_1(X2) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.26/0.65    inference(superposition,[],[f50,f54])).
% 2.26/0.65  fof(f54,plain,(
% 2.26/0.65    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f23])).
% 2.26/0.65  fof(f23,plain,(
% 2.26/0.65    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.26/0.65    inference(ennf_transformation,[],[f5])).
% 2.26/0.65  fof(f5,axiom,(
% 2.26/0.65    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.26/0.65  fof(f50,plain,(
% 2.26/0.65    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f18])).
% 2.26/0.65  fof(f18,plain,(
% 2.26/0.65    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.26/0.65    inference(flattening,[],[f17])).
% 2.26/0.65  fof(f17,plain,(
% 2.26/0.65    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.26/0.65    inference(ennf_transformation,[],[f7])).
% 2.26/0.65  fof(f7,axiom,(
% 2.26/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 2.26/0.65  fof(f74,plain,(
% 2.26/0.65    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~spl4_3),
% 2.26/0.65    inference(avatar_component_clause,[],[f70])).
% 2.26/0.65  fof(f1088,plain,(
% 2.26/0.65    ~spl4_7 | ~spl4_5 | spl4_103),
% 2.26/0.65    inference(avatar_split_clause,[],[f1086,f1068,f83,f91])).
% 2.26/0.65  fof(f1068,plain,(
% 2.26/0.65    spl4_103 <=> r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).
% 2.26/0.65  fof(f1086,plain,(
% 2.26/0.65    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl4_103),
% 2.26/0.65    inference(resolution,[],[f1069,f49])).
% 2.26/0.65  fof(f49,plain,(
% 2.26/0.65    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f16])).
% 2.26/0.65  fof(f16,plain,(
% 2.26/0.65    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.26/0.65    inference(ennf_transformation,[],[f6])).
% 2.26/0.65  fof(f6,axiom,(
% 2.26/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 2.26/0.65  fof(f1069,plain,(
% 2.26/0.65    ~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | spl4_103),
% 2.26/0.65    inference(avatar_component_clause,[],[f1068])).
% 2.26/0.65  fof(f1070,plain,(
% 2.26/0.65    ~spl4_103 | ~spl4_1 | ~spl4_98),
% 2.26/0.65    inference(avatar_split_clause,[],[f1063,f1025,f64,f1068])).
% 2.26/0.65  fof(f1025,plain,(
% 2.26/0.65    spl4_98 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK0)) | ~r1_tarski(sK2,X0))),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).
% 2.26/0.65  fof(f1063,plain,(
% 2.26/0.65    ~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) | (~spl4_1 | ~spl4_98)),
% 2.26/0.65    inference(resolution,[],[f1026,f73])).
% 2.26/0.65  fof(f73,plain,(
% 2.26/0.65    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl4_1),
% 2.26/0.65    inference(avatar_component_clause,[],[f64])).
% 2.26/0.65  fof(f1026,plain,(
% 2.26/0.65    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(X0,k1_relat_1(sK0))) ) | ~spl4_98),
% 2.26/0.65    inference(avatar_component_clause,[],[f1025])).
% 2.26/0.65  fof(f1060,plain,(
% 2.26/0.65    ~spl4_7 | spl4_3 | ~spl4_89),
% 2.26/0.65    inference(avatar_split_clause,[],[f1057,f959,f70,f91])).
% 2.26/0.65  fof(f959,plain,(
% 2.26/0.65    spl4_89 <=> r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).
% 2.26/0.65  fof(f1057,plain,(
% 2.26/0.65    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~v1_relat_1(sK0) | ~spl4_89),
% 2.26/0.65    inference(superposition,[],[f960,f54])).
% 2.26/0.65  fof(f960,plain,(
% 2.26/0.65    r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~spl4_89),
% 2.26/0.65    inference(avatar_component_clause,[],[f959])).
% 2.26/0.65  fof(f1052,plain,(
% 2.26/0.65    ~spl4_7 | ~spl4_2 | spl4_90),
% 2.26/0.65    inference(avatar_split_clause,[],[f994,f962,f67,f91])).
% 2.26/0.65  fof(f67,plain,(
% 2.26/0.65    spl4_2 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.26/0.65  fof(f994,plain,(
% 2.26/0.65    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | spl4_90),
% 2.26/0.65    inference(trivial_inequality_removal,[],[f993])).
% 2.26/0.65  fof(f993,plain,(
% 2.26/0.65    sK2 != sK2 | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | spl4_90),
% 2.26/0.65    inference(superposition,[],[f963,f55])).
% 2.26/0.65  fof(f55,plain,(
% 2.26/0.65    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f25])).
% 2.26/0.65  fof(f25,plain,(
% 2.26/0.65    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.26/0.65    inference(flattening,[],[f24])).
% 2.26/0.65  fof(f24,plain,(
% 2.26/0.65    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.26/0.65    inference(ennf_transformation,[],[f9])).
% 2.26/0.65  fof(f9,axiom,(
% 2.26/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 2.26/0.65  fof(f963,plain,(
% 2.26/0.65    sK2 != k1_relat_1(k7_relat_1(sK0,sK2)) | spl4_90),
% 2.26/0.65    inference(avatar_component_clause,[],[f962])).
% 2.26/0.65  fof(f1027,plain,(
% 2.26/0.65    spl4_2 | spl4_98 | spl4_2),
% 2.26/0.65    inference(avatar_split_clause,[],[f1022,f67,f1025,f67])).
% 2.26/0.65  fof(f1022,plain,(
% 2.26/0.65    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK0)) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_relat_1(sK0))) ) | spl4_2),
% 2.26/0.65    inference(resolution,[],[f999,f61])).
% 2.26/0.65  fof(f61,plain,(
% 2.26/0.65    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f41])).
% 2.26/0.65  fof(f41,plain,(
% 2.26/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.26/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 2.26/0.65  fof(f40,plain,(
% 2.26/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.26/0.65    introduced(choice_axiom,[])).
% 2.26/0.65  fof(f39,plain,(
% 2.26/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.26/0.65    inference(rectify,[],[f38])).
% 2.26/0.65  fof(f38,plain,(
% 2.26/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.26/0.65    inference(nnf_transformation,[],[f31])).
% 2.26/0.65  fof(f31,plain,(
% 2.26/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.26/0.65    inference(ennf_transformation,[],[f1])).
% 2.26/0.65  fof(f1,axiom,(
% 2.26/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.26/0.65  fof(f999,plain,(
% 2.26/0.65    ( ! [X0,X1] : (~r2_hidden(sK3(sK2,k1_relat_1(sK0)),X1) | ~r1_tarski(X0,k1_relat_1(sK0)) | ~r1_tarski(X1,X0)) ) | spl4_2),
% 2.26/0.65    inference(resolution,[],[f996,f60])).
% 2.26/0.65  fof(f60,plain,(
% 2.26/0.65    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f41])).
% 2.26/0.65  fof(f996,plain,(
% 2.26/0.65    ( ! [X0] : (~r2_hidden(sK3(sK2,k1_relat_1(sK0)),X0) | ~r1_tarski(X0,k1_relat_1(sK0))) ) | spl4_2),
% 2.26/0.65    inference(resolution,[],[f68,f96])).
% 2.26/0.65  fof(f96,plain,(
% 2.26/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r2_hidden(sK3(X0,X1),X2)) )),
% 2.26/0.65    inference(resolution,[],[f60,f62])).
% 2.26/0.65  fof(f62,plain,(
% 2.26/0.65    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f41])).
% 2.26/0.65  fof(f68,plain,(
% 2.26/0.65    ~r1_tarski(sK2,k1_relat_1(sK0)) | spl4_2),
% 2.26/0.65    inference(avatar_component_clause,[],[f67])).
% 2.26/0.65  fof(f988,plain,(
% 2.26/0.65    ~spl4_7 | ~spl4_6 | spl4_88),
% 2.26/0.65    inference(avatar_split_clause,[],[f987,f956,f87,f91])).
% 2.26/0.65  fof(f87,plain,(
% 2.26/0.65    spl4_6 <=> v1_funct_1(sK0)),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.26/0.65  fof(f956,plain,(
% 2.26/0.65    spl4_88 <=> v1_funct_1(k7_relat_1(sK0,sK2))),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 2.26/0.65  fof(f987,plain,(
% 2.26/0.65    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl4_88),
% 2.26/0.65    inference(resolution,[],[f957,f58])).
% 2.26/0.65  fof(f58,plain,(
% 2.26/0.65    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f28])).
% 2.26/0.65  fof(f28,plain,(
% 2.26/0.65    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.26/0.65    inference(flattening,[],[f27])).
% 2.26/0.65  fof(f27,plain,(
% 2.26/0.65    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.26/0.65    inference(ennf_transformation,[],[f10])).
% 2.26/0.65  fof(f10,axiom,(
% 2.26/0.65    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 2.26/0.65  fof(f957,plain,(
% 2.26/0.65    ~v1_funct_1(k7_relat_1(sK0,sK2)) | spl4_88),
% 2.26/0.65    inference(avatar_component_clause,[],[f956])).
% 2.26/0.65  fof(f986,plain,(
% 2.26/0.65    ~spl4_7 | spl4_84),
% 2.26/0.65    inference(avatar_split_clause,[],[f985,f941,f91])).
% 2.26/0.65  fof(f985,plain,(
% 2.26/0.65    ~v1_relat_1(sK0) | spl4_84),
% 2.26/0.65    inference(resolution,[],[f942,f52])).
% 2.26/0.65  fof(f52,plain,(
% 2.26/0.65    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f21])).
% 2.26/0.65  fof(f21,plain,(
% 2.26/0.65    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.26/0.65    inference(ennf_transformation,[],[f3])).
% 2.26/0.65  fof(f3,axiom,(
% 2.26/0.65    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.26/0.65  fof(f942,plain,(
% 2.26/0.65    ~v1_relat_1(k7_relat_1(sK0,sK2)) | spl4_84),
% 2.26/0.65    inference(avatar_component_clause,[],[f941])).
% 2.26/0.65  fof(f964,plain,(
% 2.26/0.65    ~spl4_5 | ~spl4_4 | ~spl4_84 | ~spl4_88 | spl4_89 | ~spl4_90 | ~spl4_81),
% 2.26/0.65    inference(avatar_split_clause,[],[f934,f914,f962,f959,f956,f941,f79,f83])).
% 2.26/0.65  fof(f79,plain,(
% 2.26/0.65    spl4_4 <=> v1_funct_1(sK1)),
% 2.26/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.26/0.65  fof(f934,plain,(
% 2.26/0.65    sK2 != k1_relat_1(k7_relat_1(sK0,sK2)) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_81),
% 2.26/0.65    inference(superposition,[],[f51,f915])).
% 2.26/0.65  fof(f51,plain,(
% 2.26/0.65    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f20])).
% 2.26/0.65  fof(f20,plain,(
% 2.26/0.65    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.26/0.65    inference(flattening,[],[f19])).
% 2.26/0.65  fof(f19,plain,(
% 2.26/0.65    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.26/0.65    inference(ennf_transformation,[],[f11])).
% 2.26/0.65  fof(f11,axiom,(
% 2.26/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
% 2.26/0.65  fof(f930,plain,(
% 2.26/0.65    ~spl4_7 | ~spl4_5 | spl4_80),
% 2.26/0.65    inference(avatar_split_clause,[],[f929,f911,f83,f91])).
% 2.26/0.65  fof(f929,plain,(
% 2.26/0.65    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl4_80),
% 2.26/0.65    inference(resolution,[],[f912,f59])).
% 2.26/0.65  fof(f59,plain,(
% 2.26/0.65    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.26/0.65    inference(cnf_transformation,[],[f30])).
% 2.26/0.65  fof(f30,plain,(
% 2.26/0.65    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.26/0.65    inference(flattening,[],[f29])).
% 2.26/0.65  fof(f29,plain,(
% 2.26/0.65    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.26/0.65    inference(ennf_transformation,[],[f2])).
% 2.26/0.65  fof(f2,axiom,(
% 2.26/0.65    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.26/0.65  fof(f912,plain,(
% 2.26/0.65    ~v1_relat_1(k5_relat_1(sK0,sK1)) | spl4_80),
% 2.26/0.65    inference(avatar_component_clause,[],[f911])).
% 2.26/0.65  fof(f916,plain,(
% 2.26/0.65    ~spl4_7 | ~spl4_80 | spl4_81 | ~spl4_1 | ~spl4_5),
% 2.26/0.65    inference(avatar_split_clause,[],[f892,f83,f64,f914,f911,f91])).
% 2.26/0.65  fof(f892,plain,(
% 2.26/0.65    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(sK0) | (~spl4_1 | ~spl4_5)),
% 2.26/0.65    inference(resolution,[],[f228,f73])).
% 2.26/0.65  fof(f228,plain,(
% 2.26/0.65    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(k5_relat_1(X0,sK1))) | k1_relat_1(k5_relat_1(k7_relat_1(X0,X1),sK1)) = X1 | ~v1_relat_1(k5_relat_1(X0,sK1)) | ~v1_relat_1(X0)) ) | ~spl4_5),
% 2.26/0.65    inference(superposition,[],[f55,f145])).
% 2.26/0.65  fof(f93,plain,(
% 2.26/0.65    spl4_7),
% 2.26/0.65    inference(avatar_split_clause,[],[f42,f91])).
% 2.26/0.65  fof(f42,plain,(
% 2.26/0.65    v1_relat_1(sK0)),
% 2.26/0.65    inference(cnf_transformation,[],[f37])).
% 2.26/0.65  fof(f37,plain,(
% 2.26/0.65    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.26/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36,f35,f34])).
% 2.26/0.65  fof(f34,plain,(
% 2.26/0.65    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.26/0.65    introduced(choice_axiom,[])).
% 2.26/0.65  fof(f35,plain,(
% 2.26/0.65    ? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.26/0.65    introduced(choice_axiom,[])).
% 2.26/0.65  fof(f36,plain,(
% 2.26/0.65    ? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) => ((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))))),
% 2.26/0.65    introduced(choice_axiom,[])).
% 2.26/0.65  fof(f33,plain,(
% 2.26/0.65    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.26/0.65    inference(flattening,[],[f32])).
% 2.26/0.65  fof(f32,plain,(
% 2.26/0.65    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.26/0.65    inference(nnf_transformation,[],[f15])).
% 2.26/0.65  fof(f15,plain,(
% 2.26/0.65    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.26/0.65    inference(flattening,[],[f14])).
% 2.26/0.65  fof(f14,plain,(
% 2.26/0.65    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.26/0.65    inference(ennf_transformation,[],[f13])).
% 2.26/0.65  fof(f13,negated_conjecture,(
% 2.26/0.65    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 2.26/0.65    inference(negated_conjecture,[],[f12])).
% 2.26/0.65  fof(f12,conjecture,(
% 2.26/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 2.26/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).
% 2.26/0.65  fof(f89,plain,(
% 2.26/0.65    spl4_6),
% 2.26/0.65    inference(avatar_split_clause,[],[f43,f87])).
% 2.26/0.65  fof(f43,plain,(
% 2.26/0.65    v1_funct_1(sK0)),
% 2.26/0.65    inference(cnf_transformation,[],[f37])).
% 2.26/0.65  fof(f85,plain,(
% 2.26/0.65    spl4_5),
% 2.26/0.65    inference(avatar_split_clause,[],[f44,f83])).
% 2.26/0.65  fof(f44,plain,(
% 2.26/0.65    v1_relat_1(sK1)),
% 2.26/0.65    inference(cnf_transformation,[],[f37])).
% 2.26/0.65  fof(f81,plain,(
% 2.26/0.65    spl4_4),
% 2.26/0.65    inference(avatar_split_clause,[],[f45,f79])).
% 2.26/0.65  fof(f45,plain,(
% 2.26/0.65    v1_funct_1(sK1)),
% 2.26/0.65    inference(cnf_transformation,[],[f37])).
% 2.26/0.65  fof(f77,plain,(
% 2.26/0.65    spl4_1 | spl4_2),
% 2.26/0.65    inference(avatar_split_clause,[],[f46,f67,f64])).
% 2.26/0.65  fof(f46,plain,(
% 2.26/0.65    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.26/0.65    inference(cnf_transformation,[],[f37])).
% 2.26/0.65  fof(f75,plain,(
% 2.26/0.65    spl4_1 | spl4_3),
% 2.26/0.65    inference(avatar_split_clause,[],[f47,f70,f64])).
% 2.26/0.65  fof(f47,plain,(
% 2.26/0.65    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.26/0.65    inference(cnf_transformation,[],[f37])).
% 2.26/0.65  fof(f72,plain,(
% 2.26/0.65    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 2.26/0.65    inference(avatar_split_clause,[],[f48,f70,f67,f64])).
% 2.26/0.65  fof(f48,plain,(
% 2.26/0.65    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.26/0.65    inference(cnf_transformation,[],[f37])).
% 2.26/0.65  % SZS output end Proof for theBenchmark
% 2.26/0.65  % (23513)------------------------------
% 2.26/0.65  % (23513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.65  % (23513)Termination reason: Refutation
% 2.26/0.65  
% 2.26/0.65  % (23513)Memory used [KB]: 12025
% 2.26/0.65  % (23513)Time elapsed: 0.231 s
% 2.26/0.65  % (23513)------------------------------
% 2.26/0.65  % (23513)------------------------------
% 2.26/0.66  % (23493)Success in time 0.293 s
%------------------------------------------------------------------------------
