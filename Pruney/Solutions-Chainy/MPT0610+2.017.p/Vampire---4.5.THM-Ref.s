%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 155 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :    7
%              Number of atoms          :  241 ( 456 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f53,f57,f65,f69,f81,f132,f188,f264,f302,f322,f338,f354,f361,f380])).

fof(f380,plain,
    ( spl2_1
    | ~ spl2_6
    | ~ spl2_61 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | spl2_1
    | ~ spl2_6
    | ~ spl2_61 ),
    inference(subsumption_resolution,[],[f365,f33])).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f365,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_6
    | ~ spl2_61 ),
    inference(resolution,[],[f360,f56])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f360,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl2_61
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f361,plain,
    ( spl2_61
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_60 ),
    inference(avatar_split_clause,[],[f356,f352,f51,f41,f358])).

fof(f41,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f51,plain,
    ( spl2_5
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f352,plain,
    ( spl2_60
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X3,k2_zfmisc_1(k1_relat_1(sK1),X2))
        | r1_xboole_0(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f356,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_60 ),
    inference(subsumption_resolution,[],[f355,f43])).

fof(f43,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f355,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_5
    | ~ spl2_60 ),
    inference(resolution,[],[f353,f52])).

fof(f52,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f353,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,k2_zfmisc_1(k1_relat_1(sK1),X2))
        | r1_xboole_0(X3,sK0) )
    | ~ spl2_60 ),
    inference(avatar_component_clause,[],[f352])).

fof(f354,plain,
    ( spl2_60
    | ~ spl2_9
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f348,f336,f67,f352])).

fof(f67,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f336,plain,
    ( spl2_58
  <=> ! [X6] : k2_zfmisc_1(k1_relat_1(sK1),X6) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f348,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,k2_zfmisc_1(k1_relat_1(sK1),X2))
        | r1_xboole_0(X3,sK0) )
    | ~ spl2_9
    | ~ spl2_58 ),
    inference(superposition,[],[f68,f337])).

fof(f337,plain,
    ( ! [X6] : k2_zfmisc_1(k1_relat_1(sK1),X6) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X6),sK0)
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f336])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f338,plain,
    ( spl2_58
    | ~ spl2_8
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f325,f320,f63,f336])).

fof(f63,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f320,plain,
    ( spl2_55
  <=> ! [X7] : r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X7),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f325,plain,
    ( ! [X6] : k2_zfmisc_1(k1_relat_1(sK1),X6) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X6),sK0)
    | ~ spl2_8
    | ~ spl2_55 ),
    inference(resolution,[],[f321,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f321,plain,
    ( ! [X7] : r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X7),sK0)
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f320])).

fof(f322,plain,
    ( spl2_55
    | ~ spl2_6
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f306,f300,f55,f320])).

fof(f300,plain,
    ( spl2_51
  <=> ! [X0] : r1_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f306,plain,
    ( ! [X7] : r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X7),sK0)
    | ~ spl2_6
    | ~ spl2_51 ),
    inference(resolution,[],[f301,f56])).

fof(f301,plain,
    ( ! [X0] : r1_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK1),X0))
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f300])).

fof(f302,plain,
    ( spl2_51
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f298,f262,f51,f46,f300])).

fof(f46,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f262,plain,
    ( spl2_44
  <=> ! [X3,X5,X4] :
        ( ~ r1_tarski(X5,k2_zfmisc_1(k1_relat_1(sK0),X3))
        | r1_xboole_0(X5,k2_zfmisc_1(k1_relat_1(sK1),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f298,plain,
    ( ! [X0] : r1_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK1),X0))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_44 ),
    inference(subsumption_resolution,[],[f297,f48])).

fof(f48,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f297,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK1),X0))
        | ~ v1_relat_1(sK0) )
    | ~ spl2_5
    | ~ spl2_44 ),
    inference(resolution,[],[f263,f52])).

fof(f263,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(X5,k2_zfmisc_1(k1_relat_1(sK0),X3))
        | r1_xboole_0(X5,k2_zfmisc_1(k1_relat_1(sK1),X4)) )
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f262])).

fof(f264,plain,
    ( spl2_44
    | ~ spl2_9
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f258,f186,f67,f262])).

fof(f186,plain,
    ( spl2_30
  <=> ! [X1,X0] : k2_zfmisc_1(k1_relat_1(sK0),X0) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X0),k2_zfmisc_1(k1_relat_1(sK1),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f258,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(X5,k2_zfmisc_1(k1_relat_1(sK0),X3))
        | r1_xboole_0(X5,k2_zfmisc_1(k1_relat_1(sK1),X4)) )
    | ~ spl2_9
    | ~ spl2_30 ),
    inference(superposition,[],[f68,f187])).

fof(f187,plain,
    ( ! [X0,X1] : k2_zfmisc_1(k1_relat_1(sK0),X0) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X0),k2_zfmisc_1(k1_relat_1(sK1),X1))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f186])).

fof(f188,plain,
    ( spl2_30
    | ~ spl2_2
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f179,f130,f36,f186])).

fof(f36,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f130,plain,
    ( spl2_20
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f179,plain,
    ( ! [X0,X1] : k2_zfmisc_1(k1_relat_1(sK0),X0) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X0),k2_zfmisc_1(k1_relat_1(sK1),X1))
    | ~ spl2_2
    | ~ spl2_20 ),
    inference(resolution,[],[f131,f38])).

fof(f38,plain,
    ( r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f131,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl2_20
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f127,f79,f63,f130])).

fof(f79,plain,
    ( spl2_12
  <=> ! [X1,X3,X0,X2] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f127,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) )
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(resolution,[],[f80,f64])).

fof(f80,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f79])).

fof(f81,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f28,f79])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f69,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f65,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f63])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f49,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f31])).

fof(f21,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:36:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.41  % (14142)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (14137)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.42  % (14142)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f381,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f53,f57,f65,f69,f81,f132,f188,f264,f302,f322,f338,f354,f361,f380])).
% 0.22/0.42  fof(f380,plain,(
% 0.22/0.42    spl2_1 | ~spl2_6 | ~spl2_61),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f379])).
% 0.22/0.42  fof(f379,plain,(
% 0.22/0.42    $false | (spl2_1 | ~spl2_6 | ~spl2_61)),
% 0.22/0.42    inference(subsumption_resolution,[],[f365,f33])).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f31])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.42  fof(f365,plain,(
% 0.22/0.42    r1_xboole_0(sK0,sK1) | (~spl2_6 | ~spl2_61)),
% 0.22/0.42    inference(resolution,[],[f360,f56])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f55])).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    spl2_6 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.42  fof(f360,plain,(
% 0.22/0.42    r1_xboole_0(sK1,sK0) | ~spl2_61),
% 0.22/0.42    inference(avatar_component_clause,[],[f358])).
% 0.22/0.42  fof(f358,plain,(
% 0.22/0.42    spl2_61 <=> r1_xboole_0(sK1,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 0.22/0.42  fof(f361,plain,(
% 0.22/0.42    spl2_61 | ~spl2_3 | ~spl2_5 | ~spl2_60),
% 0.22/0.42    inference(avatar_split_clause,[],[f356,f352,f51,f41,f358])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    spl2_3 <=> v1_relat_1(sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    spl2_5 <=> ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.42  fof(f352,plain,(
% 0.22/0.42    spl2_60 <=> ! [X3,X2] : (~r1_tarski(X3,k2_zfmisc_1(k1_relat_1(sK1),X2)) | r1_xboole_0(X3,sK0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).
% 0.22/0.42  fof(f356,plain,(
% 0.22/0.42    r1_xboole_0(sK1,sK0) | (~spl2_3 | ~spl2_5 | ~spl2_60)),
% 0.22/0.42    inference(subsumption_resolution,[],[f355,f43])).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    v1_relat_1(sK1) | ~spl2_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f41])).
% 0.22/0.42  fof(f355,plain,(
% 0.22/0.42    r1_xboole_0(sK1,sK0) | ~v1_relat_1(sK1) | (~spl2_5 | ~spl2_60)),
% 0.22/0.42    inference(resolution,[],[f353,f52])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f51])).
% 0.22/0.42  fof(f353,plain,(
% 0.22/0.42    ( ! [X2,X3] : (~r1_tarski(X3,k2_zfmisc_1(k1_relat_1(sK1),X2)) | r1_xboole_0(X3,sK0)) ) | ~spl2_60),
% 0.22/0.42    inference(avatar_component_clause,[],[f352])).
% 0.22/0.42  fof(f354,plain,(
% 0.22/0.42    spl2_60 | ~spl2_9 | ~spl2_58),
% 0.22/0.42    inference(avatar_split_clause,[],[f348,f336,f67,f352])).
% 0.22/0.42  fof(f67,plain,(
% 0.22/0.42    spl2_9 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.42  fof(f336,plain,(
% 0.22/0.42    spl2_58 <=> ! [X6] : k2_zfmisc_1(k1_relat_1(sK1),X6) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X6),sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 0.22/0.42  fof(f348,plain,(
% 0.22/0.42    ( ! [X2,X3] : (~r1_tarski(X3,k2_zfmisc_1(k1_relat_1(sK1),X2)) | r1_xboole_0(X3,sK0)) ) | (~spl2_9 | ~spl2_58)),
% 0.22/0.42    inference(superposition,[],[f68,f337])).
% 0.22/0.42  fof(f337,plain,(
% 0.22/0.42    ( ! [X6] : (k2_zfmisc_1(k1_relat_1(sK1),X6) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X6),sK0)) ) | ~spl2_58),
% 0.22/0.42    inference(avatar_component_clause,[],[f336])).
% 0.22/0.42  fof(f68,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) ) | ~spl2_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f67])).
% 0.22/0.42  fof(f338,plain,(
% 0.22/0.42    spl2_58 | ~spl2_8 | ~spl2_55),
% 0.22/0.42    inference(avatar_split_clause,[],[f325,f320,f63,f336])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    spl2_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.42  fof(f320,plain,(
% 0.22/0.42    spl2_55 <=> ! [X7] : r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X7),sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 0.22/0.42  fof(f325,plain,(
% 0.22/0.42    ( ! [X6] : (k2_zfmisc_1(k1_relat_1(sK1),X6) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X6),sK0)) ) | (~spl2_8 | ~spl2_55)),
% 0.22/0.42    inference(resolution,[],[f321,f64])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl2_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f63])).
% 0.22/0.42  fof(f321,plain,(
% 0.22/0.42    ( ! [X7] : (r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X7),sK0)) ) | ~spl2_55),
% 0.22/0.42    inference(avatar_component_clause,[],[f320])).
% 0.22/0.42  fof(f322,plain,(
% 0.22/0.42    spl2_55 | ~spl2_6 | ~spl2_51),
% 0.22/0.42    inference(avatar_split_clause,[],[f306,f300,f55,f320])).
% 0.22/0.42  fof(f300,plain,(
% 0.22/0.42    spl2_51 <=> ! [X0] : r1_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK1),X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 0.22/0.42  fof(f306,plain,(
% 0.22/0.42    ( ! [X7] : (r1_xboole_0(k2_zfmisc_1(k1_relat_1(sK1),X7),sK0)) ) | (~spl2_6 | ~spl2_51)),
% 0.22/0.42    inference(resolution,[],[f301,f56])).
% 0.22/0.42  fof(f301,plain,(
% 0.22/0.42    ( ! [X0] : (r1_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK1),X0))) ) | ~spl2_51),
% 0.22/0.42    inference(avatar_component_clause,[],[f300])).
% 0.22/0.42  fof(f302,plain,(
% 0.22/0.42    spl2_51 | ~spl2_4 | ~spl2_5 | ~spl2_44),
% 0.22/0.42    inference(avatar_split_clause,[],[f298,f262,f51,f46,f300])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    spl2_4 <=> v1_relat_1(sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.42  fof(f262,plain,(
% 0.22/0.42    spl2_44 <=> ! [X3,X5,X4] : (~r1_tarski(X5,k2_zfmisc_1(k1_relat_1(sK0),X3)) | r1_xboole_0(X5,k2_zfmisc_1(k1_relat_1(sK1),X4)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.22/0.42  fof(f298,plain,(
% 0.22/0.42    ( ! [X0] : (r1_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK1),X0))) ) | (~spl2_4 | ~spl2_5 | ~spl2_44)),
% 0.22/0.42    inference(subsumption_resolution,[],[f297,f48])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    v1_relat_1(sK0) | ~spl2_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f46])).
% 0.22/0.42  fof(f297,plain,(
% 0.22/0.42    ( ! [X0] : (r1_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK1),X0)) | ~v1_relat_1(sK0)) ) | (~spl2_5 | ~spl2_44)),
% 0.22/0.42    inference(resolution,[],[f263,f52])).
% 0.22/0.42  fof(f263,plain,(
% 0.22/0.42    ( ! [X4,X5,X3] : (~r1_tarski(X5,k2_zfmisc_1(k1_relat_1(sK0),X3)) | r1_xboole_0(X5,k2_zfmisc_1(k1_relat_1(sK1),X4))) ) | ~spl2_44),
% 0.22/0.42    inference(avatar_component_clause,[],[f262])).
% 0.22/0.42  fof(f264,plain,(
% 0.22/0.42    spl2_44 | ~spl2_9 | ~spl2_30),
% 0.22/0.42    inference(avatar_split_clause,[],[f258,f186,f67,f262])).
% 0.22/0.42  fof(f186,plain,(
% 0.22/0.42    spl2_30 <=> ! [X1,X0] : k2_zfmisc_1(k1_relat_1(sK0),X0) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X0),k2_zfmisc_1(k1_relat_1(sK1),X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.42  fof(f258,plain,(
% 0.22/0.42    ( ! [X4,X5,X3] : (~r1_tarski(X5,k2_zfmisc_1(k1_relat_1(sK0),X3)) | r1_xboole_0(X5,k2_zfmisc_1(k1_relat_1(sK1),X4))) ) | (~spl2_9 | ~spl2_30)),
% 0.22/0.42    inference(superposition,[],[f68,f187])).
% 0.22/0.42  fof(f187,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_zfmisc_1(k1_relat_1(sK0),X0) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X0),k2_zfmisc_1(k1_relat_1(sK1),X1))) ) | ~spl2_30),
% 0.22/0.42    inference(avatar_component_clause,[],[f186])).
% 0.22/0.42  fof(f188,plain,(
% 0.22/0.42    spl2_30 | ~spl2_2 | ~spl2_20),
% 0.22/0.42    inference(avatar_split_clause,[],[f179,f130,f36,f186])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    spl2_2 <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.42  fof(f130,plain,(
% 0.22/0.42    spl2_20 <=> ! [X1,X3,X0,X2] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.42  fof(f179,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_zfmisc_1(k1_relat_1(sK0),X0) = k4_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),X0),k2_zfmisc_1(k1_relat_1(sK1),X1))) ) | (~spl2_2 | ~spl2_20)),
% 0.22/0.42    inference(resolution,[],[f131,f38])).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f36])).
% 0.22/0.42  fof(f131,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ) | ~spl2_20),
% 0.22/0.42    inference(avatar_component_clause,[],[f130])).
% 0.22/0.42  fof(f132,plain,(
% 0.22/0.42    spl2_20 | ~spl2_8 | ~spl2_12),
% 0.22/0.42    inference(avatar_split_clause,[],[f127,f79,f63,f130])).
% 0.22/0.42  fof(f79,plain,(
% 0.22/0.42    spl2_12 <=> ! [X1,X3,X0,X2] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.42  fof(f127,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ) | (~spl2_8 | ~spl2_12)),
% 0.22/0.42    inference(resolution,[],[f80,f64])).
% 0.22/0.42  fof(f80,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) ) | ~spl2_12),
% 0.22/0.42    inference(avatar_component_clause,[],[f79])).
% 0.22/0.42  fof(f81,plain,(
% 0.22/0.42    spl2_12),
% 0.22/0.42    inference(avatar_split_clause,[],[f28,f79])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    spl2_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f27,f67])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    spl2_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f24,f63])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(nnf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    spl2_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f23,f55])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    spl2_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f22,f51])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    spl2_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f18,f46])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    v1_relat_1(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl2_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f41])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    v1_relat_1(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f20,f36])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ~spl2_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f21,f31])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ~r1_xboole_0(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (14142)------------------------------
% 0.22/0.43  % (14142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (14142)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (14142)Memory used [KB]: 10746
% 0.22/0.43  % (14142)Time elapsed: 0.013 s
% 0.22/0.43  % (14142)------------------------------
% 0.22/0.43  % (14142)------------------------------
% 0.22/0.43  % (14136)Success in time 0.071 s
%------------------------------------------------------------------------------
