%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t139_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:15 EDT 2019

% Result     : Theorem 14.73s
% Output     : Refutation 14.73s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 221 expanded)
%              Number of leaves         :   10 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  205 ( 566 expanded)
%              Number of equality atoms :   21 ( 107 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f826,f3017,f22104])).

fof(f22104,plain,(
    ~ spl10_0 ),
    inference(avatar_contradiction_clause,[],[f22103])).

fof(f22103,plain,
    ( $false
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f22064,f18534])).

fof(f18534,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK5(k7_relat_1(sK2,sK0),sK1,sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)))),sK2)
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f81,f819,f3023,f335])).

fof(f335,plain,(
    ! [X80,X83,X81,X82] :
      ( ~ v1_relat_1(X81)
      | r2_hidden(X80,k10_relat_1(sK2,X82))
      | ~ r2_hidden(k4_tarski(X80,sK5(X81,X82,X83)),sK2)
      | ~ r2_hidden(X83,k10_relat_1(X81,X82)) ) ),
    inference(resolution,[],[f93,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t139_funct_1.p',d14_relat_1)).

fof(f93,plain,(
    ! [X23,X21,X22] :
      ( ~ r2_hidden(X22,X23)
      | ~ r2_hidden(k4_tarski(X21,X22),sK2)
      | r2_hidden(X21,k10_relat_1(sK2,X23)) ) ),
    inference(resolution,[],[f38,f72])).

fof(f72,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t139_funct_1.p',t139_funct_1)).

fof(f3023,plain,
    ( ~ r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(sK2,sK1))
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f3022,f39])).

fof(f39,plain,(
    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f3022,plain,
    ( ~ r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(sK2,sK1))
    | k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f938,f819])).

fof(f938,plain,
    ( ~ r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(sK2,sK1))
    | ~ r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f707,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t139_funct_1.p',d4_xboole_0)).

fof(f707,plain,(
    r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK0) ),
    inference(subsumption_resolution,[],[f700,f195])).

fof(f195,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,k10_relat_1(k7_relat_1(sK2,X10),X11))
      | r2_hidden(X9,X10) ) ),
    inference(subsumption_resolution,[],[f182,f81])).

fof(f182,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(X9,X10)
      | ~ v1_relat_1(k7_relat_1(sK2,X10))
      | ~ r2_hidden(X9,k10_relat_1(k7_relat_1(sK2,X10),X11)) ) ),
    inference(resolution,[],[f101,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,(
    ! [X35,X36,X34] :
      ( ~ r2_hidden(k4_tarski(X35,X36),k7_relat_1(sK2,X34))
      | r2_hidden(X35,X34) ) ),
    inference(subsumption_resolution,[],[f98,f81])).

fof(f98,plain,(
    ! [X35,X36,X34] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X34))
      | r2_hidden(X35,X34)
      | ~ r2_hidden(k4_tarski(X35,X36),k7_relat_1(sK2,X34)) ) ),
    inference(resolution,[],[f38,f77])).

fof(f77,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t139_funct_1.p',d11_relat_1)).

fof(f700,plain,
    ( r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK0)
    | r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X1] :
      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != X1
      | r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),X1),sK0)
      | r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),X1),X1) ) ),
    inference(superposition,[],[f39,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f819,plain,
    ( r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f818])).

fof(f818,plain,
    ( spl10_0
  <=> r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f81,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t139_funct_1.p',dt_k7_relat_1)).

fof(f22064,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK5(k7_relat_1(sK2,sK0),sK1,sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)))),sK2)
    | ~ spl10_0 ),
    inference(resolution,[],[f231,f819])).

fof(f231,plain,(
    ! [X24,X23,X22] :
      ( ~ r2_hidden(X22,k10_relat_1(k7_relat_1(sK2,X23),X24))
      | r2_hidden(k4_tarski(X22,sK5(k7_relat_1(sK2,X23),X24,X22)),sK2) ) ),
    inference(subsumption_resolution,[],[f211,f81])).

fof(f211,plain,(
    ! [X24,X23,X22] :
      ( r2_hidden(k4_tarski(X22,sK5(k7_relat_1(sK2,X23),X24,X22)),sK2)
      | ~ v1_relat_1(k7_relat_1(sK2,X23))
      | ~ r2_hidden(X22,k10_relat_1(k7_relat_1(sK2,X23),X24)) ) ),
    inference(resolution,[],[f141,f74])).

fof(f141,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k7_relat_1(sK2,X3))
      | r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f80,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t139_funct_1.p',d3_tarski)).

fof(f80,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f38,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t139_funct_1.p',t88_relat_1)).

fof(f3017,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f3016])).

fof(f3016,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f3008,f2553])).

fof(f2553,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK5(sK2,sK1,sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)))),k7_relat_1(sK2,sK0))
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f707,f825,f366])).

fof(f366,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k10_relat_1(sK2,X1))
      | r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),k7_relat_1(sK2,X2)) ) ),
    inference(subsumption_resolution,[],[f365,f81])).

fof(f365,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK2,X1))
      | ~ v1_relat_1(k7_relat_1(sK2,X2))
      | ~ r2_hidden(X0,X2)
      | r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),k7_relat_1(sK2,X2)) ) ),
    inference(subsumption_resolution,[],[f353,f38])).

fof(f353,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK2,X1))
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(k7_relat_1(sK2,X2))
      | ~ r2_hidden(X0,X2)
      | r2_hidden(k4_tarski(X0,sK5(sK2,X1,X0)),k7_relat_1(sK2,X2)) ) ),
    inference(resolution,[],[f95,f75])).

fof(f75,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    ! [X26,X27] :
      ( r2_hidden(k4_tarski(X26,sK5(sK2,X27,X26)),sK2)
      | ~ r2_hidden(X26,k10_relat_1(sK2,X27)) ) ),
    inference(resolution,[],[f38,f74])).

fof(f825,plain,
    ( r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(sK2,sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f824])).

fof(f824,plain,
    ( spl10_2
  <=> r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f3008,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK5(sK2,sK1,sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)))),k7_relat_1(sK2,sK0))
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f81,f816,f825,f245])).

fof(f245,plain,(
    ! [X19,X17,X20,X18] :
      ( ~ v1_relat_1(X19)
      | ~ r2_hidden(X17,k10_relat_1(sK2,X18))
      | ~ r2_hidden(k4_tarski(X20,sK5(sK2,X18,X17)),X19)
      | r2_hidden(X20,k10_relat_1(X19,X18)) ) ),
    inference(resolution,[],[f94,f72])).

fof(f94,plain,(
    ! [X24,X25] :
      ( r2_hidden(sK5(sK2,X24,X25),X24)
      | ~ r2_hidden(X25,k10_relat_1(sK2,X24)) ) ),
    inference(resolution,[],[f38,f73])).

fof(f816,plain,
    ( ~ r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f815])).

fof(f815,plain,
    ( spl10_1
  <=> ~ r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f826,plain,
    ( spl10_0
    | spl10_2 ),
    inference(avatar_split_clause,[],[f807,f824,f818])).

fof(f807,plain,
    ( r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(sK2,sK1))
    | r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2] :
      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != X2
      | r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),X2),k10_relat_1(sK2,sK1))
      | r2_hidden(sK3(sK0,k10_relat_1(sK2,sK1),X2),X2) ) ),
    inference(superposition,[],[f39,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
