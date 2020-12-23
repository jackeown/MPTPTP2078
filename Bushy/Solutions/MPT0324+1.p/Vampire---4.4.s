%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t137_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:00 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  47 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 107 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f59,f75,f93])).

fof(f93,plain,
    ( spl7_7
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f91,f58])).

fof(f58,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl7_7
  <=> ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f91,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f90,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t137_zfmisc_1.p',t123_zfmisc_1)).

fof(f90,plain,
    ( r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))
    | ~ spl7_12 ),
    inference(resolution,[],[f74,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t137_zfmisc_1.p',d4_xboole_0)).

fof(f74,plain,
    ( sP6(sK0,k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK1,sK2))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl7_12
  <=> sP6(sK0,k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f75,plain,
    ( spl7_12
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f65,f45,f41,f73])).

fof(f41,plain,
    ( spl7_0
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f45,plain,
    ( spl7_2
  <=> r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f65,plain,
    ( sP6(sK0,k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK1,sK2))
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(resolution,[],[f49,f46])).

fof(f46,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | sP6(sK0,X0,k2_zfmisc_1(sK1,sK2)) )
    | ~ spl7_0 ),
    inference(resolution,[],[f42,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f42,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f41])).

fof(f59,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
          & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
       => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
     => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t137_zfmisc_1.p',t137_zfmisc_1)).

fof(f47,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
