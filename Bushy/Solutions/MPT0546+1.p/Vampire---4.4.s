%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t148_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:51 EDT 2019

% Result     : Theorem 14.25s
% Output     : Refutation 14.25s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 112 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  158 ( 296 expanded)
%              Number of equality atoms :   18 (  55 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3473,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f769,f3080,f3462])).

fof(f3462,plain,
    ( spl11_11
    | ~ spl11_12 ),
    inference(avatar_contradiction_clause,[],[f3461])).

fof(f3461,plain,
    ( $false
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f3427,f3429])).

fof(f3429,plain,
    ( r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f27,f57,f768,f55])).

fof(f55,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t148_relat_1.p',d11_relat_1)).

fof(f768,plain,
    ( r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f767])).

fof(f767,plain,
    ( spl11_12
  <=> r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f27,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t148_relat_1.p',dt_k7_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) != k9_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t148_relat_1.p',t148_relat_1)).

fof(f3427,plain,
    ( ~ r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f27,f759,f768,f294])).

fof(f294,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ v1_relat_1(X12)
      | r2_hidden(X10,k9_relat_1(sK1,X11))
      | ~ r2_hidden(k4_tarski(X9,X10),sK1)
      | ~ r2_hidden(k4_tarski(X9,X13),k7_relat_1(X12,X11)) ) ),
    inference(subsumption_resolution,[],[f275,f41])).

fof(f275,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X10),sK1)
      | r2_hidden(X10,k9_relat_1(sK1,X11))
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(k7_relat_1(X12,X11))
      | ~ r2_hidden(k4_tarski(X9,X13),k7_relat_1(X12,X11)) ) ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X21,X22,X20] :
      ( ~ r2_hidden(X20,X22)
      | ~ r2_hidden(k4_tarski(X20,X21),sK1)
      | r2_hidden(X21,k9_relat_1(sK1,X22)) ) ),
    inference(resolution,[],[f27,f49])).

fof(f49,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t148_relat_1.p',d13_relat_1)).

fof(f759,plain,
    ( ~ r2_hidden(sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f758])).

fof(f758,plain,
    ( spl11_11
  <=> ~ r2_hidden(sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f3080,plain,(
    ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f3079])).

fof(f3079,plain,
    ( $false
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f3003,f1008])).

fof(f1008,plain,
    ( r2_hidden(k4_tarski(sK4(sK1,sK0,sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f27,f762,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f762,plain,
    ( r2_hidden(sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f761])).

fof(f761,plain,
    ( spl11_10
  <=> r2_hidden(sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f3003,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK1,sK0,sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f1009,f1004,f74])).

fof(f74,plain,(
    ! [X28,X29,X27] :
      ( ~ r2_hidden(X28,X27)
      | ~ r2_hidden(k4_tarski(X28,X29),sK1)
      | r2_hidden(k4_tarski(X28,X29),k7_relat_1(sK1,X27)) ) ),
    inference(subsumption_resolution,[],[f71,f57])).

fof(f71,plain,(
    ! [X28,X29,X27] :
      ( ~ v1_relat_1(k7_relat_1(sK1,X27))
      | ~ r2_hidden(X28,X27)
      | ~ r2_hidden(k4_tarski(X28,X29),sK1)
      | r2_hidden(k4_tarski(X28,X29),k7_relat_1(sK1,X27)) ) ),
    inference(resolution,[],[f27,f54])).

fof(f54,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1004,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f28,f762,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t148_relat_1.p',d5_relat_1)).

fof(f28,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f1009,plain,
    ( r2_hidden(sK4(sK1,sK0,sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK0)
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f27,f762,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f769,plain,
    ( spl11_10
    | spl11_12 ),
    inference(avatar_split_clause,[],[f732,f767,f761])).

fof(f732,plain,
    ( r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))
    | r2_hidden(sK6(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( k9_relat_1(sK1,sK0) != X0
      | r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),X0),sK6(k7_relat_1(sK1,sK0),X0)),k7_relat_1(sK1,sK0))
      | r2_hidden(sK6(k7_relat_1(sK1,sK0),X0),X0) ) ),
    inference(superposition,[],[f28,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
