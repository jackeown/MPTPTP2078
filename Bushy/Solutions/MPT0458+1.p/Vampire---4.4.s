%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t46_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:02 EDT 2019

% Result     : Theorem 22.35s
% Output     : Refutation 22.35s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 128 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  200 ( 395 expanded)
%              Number of equality atoms :   17 (  60 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f782,f798,f818,f16111])).

fof(f16111,plain,
    ( spl16_19
    | ~ spl16_22 ),
    inference(avatar_contradiction_clause,[],[f16110])).

fof(f16110,plain,
    ( $false
    | ~ spl16_19
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f16100,f4839])).

fof(f4839,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK10(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK1)
    | ~ spl16_19
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f4780,f44])).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1))
          & r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1))
          & r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
             => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t46_relat_1.p',t46_relat_1)).

fof(f4780,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK10(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl16_19
    | ~ spl16_22 ),
    inference(resolution,[],[f850,f825])).

fof(f825,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),k5_relat_1(sK0,sK1))
    | ~ spl16_19 ),
    inference(resolution,[],[f778,f88])).

fof(f88,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t46_relat_1.p',d4_relat_1)).

fof(f778,plain,
    ( ~ r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl16_19 ),
    inference(avatar_component_clause,[],[f777])).

fof(f777,plain,
    ( spl16_19
  <=> ~ r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_19])])).

fof(f850,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X7),k5_relat_1(sK0,X6))
        | ~ r2_hidden(k4_tarski(sK10(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X7),X6)
        | ~ v1_relat_1(X6) )
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f849,f135])).

fof(f135,plain,(
    ! [X2] :
      ( v1_relat_1(k5_relat_1(sK0,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f47,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t46_relat_1.p',dt_k5_relat_1)).

fof(f47,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f849,plain,
    ( ! [X6,X7] :
        ( ~ v1_relat_1(X6)
        | ~ v1_relat_1(k5_relat_1(sK0,X6))
        | ~ r2_hidden(k4_tarski(sK10(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X7),X6)
        | r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X7),k5_relat_1(sK0,X6)) )
    | ~ spl16_22 ),
    inference(subsumption_resolution,[],[f840,f47])).

fof(f840,plain,
    ( ! [X6,X7] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(k5_relat_1(sK0,X6))
        | ~ r2_hidden(k4_tarski(sK10(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X7),X6)
        | r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X7),k5_relat_1(sK0,X6)) )
    | ~ spl16_22 ),
    inference(resolution,[],[f797,f82])).

fof(f82,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t46_relat_1.p',d8_relat_1)).

fof(f797,plain,
    ( r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK10(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))),sK0)
    | ~ spl16_22 ),
    inference(avatar_component_clause,[],[f796])).

fof(f796,plain,
    ( spl16_22
  <=> r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK10(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).

fof(f16100,plain,
    ( r2_hidden(k4_tarski(sK10(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK9(sK1,sK10(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))),sK1)
    | ~ spl16_22 ),
    inference(resolution,[],[f990,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK9(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK9(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f990,plain,
    ( r2_hidden(sK10(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | ~ spl16_22 ),
    inference(resolution,[],[f302,f797])).

fof(f302,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK0)
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f159,f90])).

fof(f90,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t46_relat_1.p',d5_relat_1)).

fof(f159,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f45,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t46_relat_1.p',d3_tarski)).

fof(f45,plain,(
    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f818,plain,
    ( ~ spl16_18
    | ~ spl16_20 ),
    inference(avatar_contradiction_clause,[],[f817])).

fof(f817,plain,
    ( $false
    | ~ spl16_18
    | ~ spl16_20 ),
    inference(subsumption_resolution,[],[f809,f807])).

fof(f807,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X4),k5_relat_1(sK0,sK1))
    | ~ spl16_20 ),
    inference(subsumption_resolution,[],[f802,f47])).

fof(f802,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(sK0)
        | ~ r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X4),k5_relat_1(sK0,sK1)) )
    | ~ spl16_20 ),
    inference(resolution,[],[f781,f132])).

fof(f132,plain,(
    ! [X23,X21,X22] :
      ( r2_hidden(k4_tarski(X22,sK4(X21,sK1,X22,X23)),X21)
      | ~ v1_relat_1(X21)
      | ~ r2_hidden(k4_tarski(X22,X23),k5_relat_1(X21,sK1)) ) ),
    inference(subsumption_resolution,[],[f117,f111])).

fof(f111,plain,(
    ! [X3] :
      ( v1_relat_1(k5_relat_1(X3,sK1))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f44,f61])).

fof(f117,plain,(
    ! [X23,X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_relat_1(k5_relat_1(X21,sK1))
      | r2_hidden(k4_tarski(X22,sK4(X21,sK1,X22,X23)),X21)
      | ~ r2_hidden(k4_tarski(X22,X23),k5_relat_1(X21,sK1)) ) ),
    inference(resolution,[],[f44,f84])).

fof(f84,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f781,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK0)
    | ~ spl16_20 ),
    inference(avatar_component_clause,[],[f780])).

fof(f780,plain,
    ( spl16_20
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_20])])).

fof(f809,plain,
    ( r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK9(k5_relat_1(sK0,sK1),sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))),k5_relat_1(sK0,sK1))
    | ~ spl16_18 ),
    inference(resolution,[],[f775,f87])).

fof(f775,plain,
    ( r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl16_18 ),
    inference(avatar_component_clause,[],[f774])).

fof(f774,plain,
    ( spl16_18
  <=> r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_18])])).

fof(f798,plain,
    ( spl16_18
    | spl16_22 ),
    inference(avatar_split_clause,[],[f162,f796,f774])).

fof(f162,plain,
    ( r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK10(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))),sK0)
    | r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f94,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK8(X0,X1),X1)
      | sQ15_eqProxy(k1_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f70,f93])).

fof(f93,plain,(
    ! [X1,X0] :
      ( sQ15_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ15_eqProxy])])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK10(X0,X1)),X0)
      | r2_hidden(sK8(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f94,plain,(
    ~ sQ15_eqProxy(k1_relat_1(sK0),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f46,f93])).

fof(f46,plain,(
    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f782,plain,
    ( ~ spl16_19
    | spl16_20 ),
    inference(avatar_split_clause,[],[f163,f780,f777])).

fof(f163,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK0)
      | ~ r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) ) ),
    inference(resolution,[],[f94,f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
      | ~ r2_hidden(sK8(X0,X1),X1)
      | sQ15_eqProxy(k1_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f71,f93])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
      | ~ r2_hidden(sK8(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
