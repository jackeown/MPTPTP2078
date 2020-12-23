%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t54_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:08 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   72 ( 100 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f46,f53,f60,f70,f78,f83])).

fof(f83,plain,
    ( ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f81,f45])).

fof(f45,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f81,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl2_6 ),
    inference(resolution,[],[f31,f59])).

fof(f59,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_6
  <=> r1_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t54_zfmisc_1.p',l24_zfmisc_1)).

fof(f78,plain,
    ( spl2_10
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f71,f58,f76])).

fof(f76,plain,
    ( spl2_10
  <=> r1_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f71,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_6 ),
    inference(resolution,[],[f28,f59])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t54_zfmisc_1.p',symmetry_r1_xboole_0)).

fof(f70,plain,
    ( ~ spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f63,f44,f68])).

fof(f68,plain,
    ( spl2_9
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f63,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f27,f45])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t54_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f60,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f22,f58])).

fof(f22,plain,(
    r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( r2_hidden(sK0,sK1)
    & r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) )
   => ( r2_hidden(sK0,sK1)
      & r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,X1)
      & r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_hidden(X0,X1)
          & r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t54_zfmisc_1.p',t54_zfmisc_1)).

fof(f53,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f51,plain,
    ( spl2_4
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f25,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t54_zfmisc_1.p',d2_xboole_0)).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f24,f37])).

fof(f37,plain,
    ( spl2_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f24,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t54_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
