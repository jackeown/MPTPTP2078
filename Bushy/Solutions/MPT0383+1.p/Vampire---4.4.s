%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t65_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:26 EDT 2019

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 (  98 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  149 ( 274 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f50,f69,f84,f100,f108,f116,f130])).

fof(f130,plain,
    ( ~ spl7_20
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f127,f99])).

fof(f99,plain,
    ( k4_tarski(sK4(sK0,sK1,sK3),sK5(sK0,sK1,sK3)) = sK3
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_20
  <=> k4_tarski(sK4(sK0,sK1,sK3),sK5(sK0,sK1,sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f127,plain,
    ( k4_tarski(sK4(sK0,sK1,sK3),sK5(sK0,sK1,sK3)) != sK3
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(resolution,[],[f117,f115])).

fof(f115,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl7_28
  <=> m1_subset_1(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k4_tarski(sK4(sK0,sK1,sK3),X0) != sK3 )
    | ~ spl7_24 ),
    inference(resolution,[],[f107,f21])).

fof(f21,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ m1_subset_1(X5,sK1)
      | k4_tarski(X4,X5) != sK3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != X3
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) )
      & r1_tarski(X2,k2_zfmisc_1(X0,X1))
      & r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4] :
              ( m1_subset_1(X4,X0)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k4_tarski(X4,X5) != X3 ) )
          & r1_tarski(X2,k2_zfmisc_1(X0,X1))
          & r2_hidden(X3,X2) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t65_subset_1.p',t65_subset_1)).

fof(f107,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_24
  <=> m1_subset_1(sK4(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f116,plain,
    ( spl7_28
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f88,f82,f114])).

fof(f82,plain,
    ( spl7_14
  <=> r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f88,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f87,f86])).

fof(f86,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_14 ),
    inference(resolution,[],[f83,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t65_subset_1.p',t7_boole)).

fof(f83,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f82])).

fof(f87,plain,
    ( v1_xboole_0(sK1)
    | m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ spl7_14 ),
    inference(resolution,[],[f83,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t65_subset_1.p',d2_subset_1)).

fof(f108,plain,
    ( spl7_24
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f74,f67,f106])).

fof(f67,plain,
    ( spl7_10
  <=> r2_hidden(sK4(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f74,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK0)
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f73,f72])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl7_10 ),
    inference(resolution,[],[f68,f33])).

fof(f68,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f73,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(sK4(sK0,sK1,sK3),sK0)
    | ~ spl7_10 ),
    inference(resolution,[],[f68,f30])).

fof(f100,plain,
    ( spl7_20
    | ~ spl7_0
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f80,f48,f36,f98])).

fof(f36,plain,
    ( spl7_0
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f48,plain,
    ( spl7_4
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f80,plain,
    ( k4_tarski(sK4(sK0,sK1,sK3),sK5(sK0,sK1,sK3)) = sK3
    | ~ spl7_0
    | ~ spl7_4 ),
    inference(resolution,[],[f53,f37])).

fof(f37,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f36])).

fof(f53,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | k4_tarski(sK4(sK0,sK1,X2),sK5(sK0,sK1,X2)) = X2 )
    | ~ spl7_4 ),
    inference(resolution,[],[f49,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t65_subset_1.p',t103_zfmisc_1)).

fof(f49,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f84,plain,
    ( spl7_14
    | ~ spl7_0
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f70,f48,f36,f82])).

fof(f70,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ spl7_0
    | ~ spl7_4 ),
    inference(resolution,[],[f52,f37])).

fof(f52,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | r2_hidden(sK5(sK0,sK1,X1),sK1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(sK5(X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,
    ( spl7_10
    | ~ spl7_0
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f65,f48,f36,f67])).

fof(f65,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK0)
    | ~ spl7_0
    | ~ spl7_4 ),
    inference(resolution,[],[f51,f37])).

fof(f51,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(sK4(sK0,sK1,X0),sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f49,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(sK4(X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
