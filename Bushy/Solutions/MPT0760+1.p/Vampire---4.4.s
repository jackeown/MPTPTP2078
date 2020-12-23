%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t2_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:12 EDT 2019

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :  125 ( 155 expanded)
%              Number of equality atoms :   21 (  30 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f272,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f79,f86,f93,f271])).

fof(f271,plain,
    ( ~ spl3_0
    | spl3_3
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f269,f85])).

fof(f85,plain,
    ( k1_wellord1(sK1,sK0) != k1_xboole_0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_5
  <=> k1_wellord1(sK1,sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f269,plain,
    ( k1_wellord1(sK1,sK0) = k1_xboole_0
    | ~ spl3_0
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f268,f71])).

fof(f71,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f268,plain,
    ( ~ v1_relat_1(sK1)
    | k1_wellord1(sK1,sK0) = k1_xboole_0
    | ~ spl3_3 ),
    inference(resolution,[],[f199,f78])).

fof(f78,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_3
  <=> ~ r2_hidden(sK0,k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f199,plain,(
    ! [X6,X7] :
      ( r2_hidden(X7,k3_relat_1(X6))
      | ~ v1_relat_1(X6)
      | k1_wellord1(X6,X7) = k1_xboole_0 ) ),
    inference(resolution,[],[f154,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t2_wellord1.p',t6_boole)).

fof(f154,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k1_wellord1(X2,X3))
      | ~ v1_relat_1(X2)
      | r2_hidden(X3,k3_relat_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k1_wellord1(X2,X3))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X3,k3_relat_1(X2)) ) ),
    inference(resolution,[],[f103,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_wellord1(X0,X2))
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k3_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_wellord1(X0,X2))
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k3_relat_1(X0)) ) ),
    inference(resolution,[],[f63,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t2_wellord1.p',t30_relat_1)).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X1),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t2_wellord1.p',d1_wellord1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(o_2_0_wellord1(X1,X0),k1_wellord1(X0,X1))
      | v1_xboole_0(k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f55,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t2_wellord1.p',t2_subset)).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_0_wellord1(X0,X1),k1_wellord1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_0_wellord1(X0,X1),k1_wellord1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => m1_subset_1(o_2_0_wellord1(X0,X1),k1_wellord1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t2_wellord1.p',dt_o_2_0_wellord1)).

fof(f93,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f54,f91])).

fof(f91,plain,
    ( spl3_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f54,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/wellord1__t2_wellord1.p',d2_xboole_0)).

fof(f86,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    k1_wellord1(sK1,sK0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k1_xboole_0
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k1_xboole_0
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_wellord1(X1,X0) = k1_xboole_0
          | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord1(X1,X0) = k1_xboole_0
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t2_wellord1.p',t2_wellord1)).

fof(f79,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    ~ r2_hidden(sK0,k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f40,f70])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
