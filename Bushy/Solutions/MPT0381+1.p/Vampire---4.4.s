%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t63_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:26 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 102 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f55,f69,f75,f83])).

fof(f83,plain,
    ( spl4_5
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f81,f54])).

fof(f54,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_5
  <=> ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f81,plain,
    ( m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f80,f78])).

fof(f78,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl4_12 ),
    inference(resolution,[],[f74,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t63_subset_1.p',t7_boole)).

fof(f74,plain,
    ( r2_hidden(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_12
  <=> r2_hidden(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f80,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | ~ spl4_12 ),
    inference(resolution,[],[f74,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t63_subset_1.p',d2_subset_1)).

fof(f75,plain,
    ( spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f71,f67,f73])).

fof(f67,plain,
    ( spl4_10
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f71,plain,
    ( r2_hidden(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t63_subset_1.p',d1_zfmisc_1)).

fof(f68,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,
    ( spl4_10
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f45,f40,f67])).

fof(f40,plain,
    ( spl4_0
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f45,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl4_0 ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t63_subset_1.p',t37_zfmisc_1)).

fof(f41,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f40])).

fof(f55,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t63_subset_1.p',t63_subset_1)).

fof(f42,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
