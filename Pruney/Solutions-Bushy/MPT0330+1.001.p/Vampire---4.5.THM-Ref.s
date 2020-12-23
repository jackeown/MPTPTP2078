%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0330+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 105 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  144 ( 237 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f57,f62,f67,f106,f176,f196,f248])).

fof(f248,plain,(
    spl6_25 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl6_25 ),
    inference(subsumption_resolution,[],[f246,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f246,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK2,sK4))
    | spl6_25 ),
    inference(subsumption_resolution,[],[f244,f19])).

fof(f244,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK3,sK5))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK4))
    | spl6_25 ),
    inference(resolution,[],[f175,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f175,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl6_25
  <=> r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f196,plain,(
    spl6_15 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl6_15 ),
    inference(subsumption_resolution,[],[f194,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f194,plain,
    ( ~ r1_tarski(sK4,k2_xboole_0(sK2,sK4))
    | spl6_15 ),
    inference(subsumption_resolution,[],[f192,f39])).

fof(f192,plain,
    ( ~ r1_tarski(sK5,k2_xboole_0(sK3,sK5))
    | ~ r1_tarski(sK4,k2_xboole_0(sK2,sK4))
    | spl6_15 ),
    inference(resolution,[],[f105,f23])).

fof(f105,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_15
  <=> r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f176,plain,
    ( ~ spl6_25
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f159,f60,f35,f173])).

fof(f35,plain,
    ( spl6_3
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f60,plain,
    ( spl6_7
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f159,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f61,f37])).

fof(f37,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f106,plain,
    ( ~ spl6_15
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f89,f65,f30,f103])).

fof(f30,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f65,plain,
    ( spl6_8
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f89,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(resolution,[],[f66,f32])).

fof(f32,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(X0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f67,plain,
    ( spl6_8
    | spl6_6 ),
    inference(avatar_split_clause,[],[f63,f54,f65])).

fof(f54,plain,
    ( spl6_6
  <=> r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
        | ~ r1_tarski(sK1,X0) )
    | spl6_6 ),
    inference(resolution,[],[f56,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f56,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f62,plain,
    ( spl6_7
    | spl6_5 ),
    inference(avatar_split_clause,[],[f58,f50,f60])).

fof(f50,plain,
    ( spl6_5
  <=> r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
        | ~ r1_tarski(sK0,X0) )
    | spl6_5 ),
    inference(resolution,[],[f52,f21])).

fof(f52,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f57,plain,
    ( ~ spl6_5
    | ~ spl6_6
    | spl6_1 ),
    inference(avatar_split_clause,[],[f46,f25,f54,f50])).

fof(f25,plain,
    ( spl6_1
  <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f46,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_1 ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f38,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f33,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f18,f25])).

fof(f18,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
