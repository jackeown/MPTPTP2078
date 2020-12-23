%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0519+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 149 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 ( 366 expanded)
%              Number of equality atoms :   19 (  61 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f809,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f204,f695,f697,f731,f803,f808])).

fof(f808,plain,
    ( ~ spl9_1
    | spl9_4 ),
    inference(avatar_contradiction_clause,[],[f807])).

fof(f807,plain,
    ( $false
    | ~ spl9_1
    | spl9_4 ),
    inference(subsumption_resolution,[],[f690,f737])).

fof(f737,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0)
    | ~ spl9_1 ),
    inference(resolution,[],[f199,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f199,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k3_xboole_0(k2_relat_1(sK1),sK0))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl9_1
  <=> r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k3_xboole_0(k2_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f690,plain,
    ( ~ r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f688])).

fof(f688,plain,
    ( spl9_4
  <=> r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f803,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f802])).

fof(f802,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f797,f752])).

fof(f752,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK1)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f743,f689])).

fof(f689,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f688])).

fof(f743,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK1)
        | ~ r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0) )
    | ~ spl9_2 ),
    inference(resolution,[],[f203,f68])).

fof(f68,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(k4_tarski(X4,X3),k8_relat_1(X2,sK1))
      | ~ r2_hidden(k4_tarski(X4,X3),sK1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(subsumption_resolution,[],[f59,f57])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(resolution,[],[f15,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != k3_xboole_0(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f59,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(k8_relat_1(X2,sK1))
      | ~ r2_hidden(X3,X2)
      | ~ r2_hidden(k4_tarski(X4,X3),sK1)
      | r2_hidden(k4_tarski(X4,X3),k8_relat_1(X2,sK1)) ) ),
    inference(resolution,[],[f15,f36])).

fof(f36,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f203,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),k8_relat_1(sK0,sK1))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl9_2
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),k8_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f797,plain,
    ( r2_hidden(k4_tarski(sK5(sK1,sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK1)
    | ~ spl9_1 ),
    inference(resolution,[],[f736,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f736,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k2_relat_1(sK1))
    | ~ spl9_1 ),
    inference(resolution,[],[f199,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f731,plain,
    ( spl9_1
    | spl9_5 ),
    inference(avatar_contradiction_clause,[],[f730])).

fof(f730,plain,
    ( $false
    | spl9_1
    | spl9_5 ),
    inference(subsumption_resolution,[],[f729,f704])).

fof(f704,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK1)
    | spl9_5 ),
    inference(resolution,[],[f694,f40])).

fof(f40,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f694,plain,
    ( ~ r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k2_relat_1(sK1))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f692])).

fof(f692,plain,
    ( spl9_5
  <=> r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f729,plain,
    ( r2_hidden(k4_tarski(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK1)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f728,f57])).

fof(f728,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK1)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f716,f15])).

fof(f716,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),sK1)
    | spl9_1 ),
    inference(resolution,[],[f211,f37])).

fof(f37,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f211,plain,
    ( r2_hidden(k4_tarski(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),k8_relat_1(sK0,sK1))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f205,f45])).

fof(f45,plain,(
    ~ sQ8_eqProxy(k2_relat_1(k8_relat_1(sK0,sK1)),k3_xboole_0(k2_relat_1(sK1),sK0)) ),
    inference(equality_proxy_replacement,[],[f16,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f16,plain,(
    k2_relat_1(k8_relat_1(sK0,sK1)) != k3_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f205,plain,
    ( r2_hidden(k4_tarski(sK6(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),k8_relat_1(sK0,sK1))
    | sQ8_eqProxy(k2_relat_1(k8_relat_1(sK0,sK1)),k3_xboole_0(k2_relat_1(sK1),sK0))
    | spl9_1 ),
    inference(resolution,[],[f200,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | sQ8_eqProxy(k2_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f28,f44])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f200,plain,
    ( ~ r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k3_xboole_0(k2_relat_1(sK1),sK0))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f198])).

fof(f697,plain,
    ( spl9_1
    | spl9_4 ),
    inference(avatar_contradiction_clause,[],[f696])).

fof(f696,plain,
    ( $false
    | spl9_1
    | spl9_4 ),
    inference(subsumption_resolution,[],[f690,f663])).

fof(f663,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f656,f200])).

fof(f656,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k3_xboole_0(k2_relat_1(sK1),sK0))
    | r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0) ),
    inference(resolution,[],[f106,f45])).

fof(f106,plain,(
    ! [X19,X18] :
      ( sQ8_eqProxy(k2_relat_1(k8_relat_1(X18,sK1)),X19)
      | r2_hidden(sK4(k8_relat_1(X18,sK1),X19),X19)
      | r2_hidden(sK4(k8_relat_1(X18,sK1),X19),X18) ) ),
    inference(resolution,[],[f70,f50])).

fof(f70,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(k4_tarski(X10,X9),k8_relat_1(X8,sK1))
      | r2_hidden(X9,X8) ) ),
    inference(subsumption_resolution,[],[f61,f57])).

fof(f61,plain,(
    ! [X10,X8,X9] :
      ( ~ v1_relat_1(k8_relat_1(X8,sK1))
      | r2_hidden(X9,X8)
      | ~ r2_hidden(k4_tarski(X10,X9),k8_relat_1(X8,sK1)) ) ),
    inference(resolution,[],[f15,f38])).

fof(f38,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f695,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_1 ),
    inference(avatar_split_clause,[],[f206,f198,f692,f688])).

fof(f206,plain,
    ( ~ r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k2_relat_1(sK1))
    | ~ r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),sK0)
    | spl9_1 ),
    inference(resolution,[],[f200,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f204,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f89,f202,f198])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0))),k8_relat_1(sK0,sK1))
      | ~ r2_hidden(sK4(k8_relat_1(sK0,sK1),k3_xboole_0(k2_relat_1(sK1),sK0)),k3_xboole_0(k2_relat_1(sK1),sK0)) ) ),
    inference(resolution,[],[f45,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | sQ8_eqProxy(k2_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f29,f44])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

%------------------------------------------------------------------------------
