%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t181_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:55 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 309 expanded)
%              Number of leaves         :   16 (  76 expanded)
%              Depth                    :   20
%              Number of atoms          :  427 (1200 expanded)
%              Number of equality atoms :   24 ( 109 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f592,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f64,f71,f90,f94,f108,f113,f247,f251,f585,f589])).

fof(f589,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | ~ spl11_10
    | spl11_13 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f587,f98])).

fof(f98,plain,
    ( r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl11_10
  <=> r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(sK1,k10_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f587,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f586,f56])).

fof(f56,plain,
    ( v1_relat_1(sK2)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl11_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f586,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ spl11_2
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f569,f63])).

fof(f63,plain,
    ( v1_relat_1(sK1)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl11_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f569,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ spl11_13 ),
    inference(resolution,[],[f498,f107])).

fof(f107,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl11_13
  <=> ~ r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f498,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k10_relat_1(k5_relat_1(X1,X0),X3))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k10_relat_1(X1,k10_relat_1(X0,X3))) ) ),
    inference(duplicate_literal_removal,[],[f497])).

fof(f497,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(X2,k10_relat_1(k5_relat_1(X1,X0),X3))
      | ~ r2_hidden(X2,k10_relat_1(X1,k10_relat_1(X0,X3)))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k10_relat_1(X1,k10_relat_1(X0,X3))) ) ),
    inference(resolution,[],[f424,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t181_relat_1.p',d14_relat_1)).

fof(f424,plain,(
    ! [X26,X24,X23,X27,X25] :
      ( ~ r2_hidden(sK5(X24,X25,X26),k10_relat_1(X23,X27))
      | ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | r2_hidden(X26,k10_relat_1(k5_relat_1(X24,X23),X27))
      | ~ r2_hidden(X26,k10_relat_1(X24,X25)) ) ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,(
    ! [X26,X24,X23,X27,X25] :
      ( ~ v1_relat_1(X23)
      | ~ r2_hidden(sK5(X24,X25,X26),k10_relat_1(X23,X27))
      | ~ v1_relat_1(X24)
      | r2_hidden(X26,k10_relat_1(k5_relat_1(X24,X23),X27))
      | ~ v1_relat_1(X24)
      | ~ r2_hidden(X26,k10_relat_1(X24,X25)) ) ),
    inference(resolution,[],[f326,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f326,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X2),X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k10_relat_1(X1,X3))
      | ~ v1_relat_1(X0)
      | r2_hidden(X4,k10_relat_1(k5_relat_1(X0,X1),X3)) ) ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k10_relat_1(X1,X3))
      | ~ r2_hidden(k4_tarski(X4,X2),X0)
      | r2_hidden(X4,k10_relat_1(k5_relat_1(X0,X1),X3))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k10_relat_1(X1,X3)) ) ),
    inference(resolution,[],[f197,f46])).

fof(f197,plain,(
    ! [X14,X17,X15,X13,X18,X16] :
      ( ~ r2_hidden(sK5(X16,X17,X14),X18)
      | ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | ~ r2_hidden(X14,k10_relat_1(X16,X17))
      | ~ r2_hidden(k4_tarski(X13,X14),X15)
      | r2_hidden(X13,k10_relat_1(k5_relat_1(X15,X16),X18)) ) ),
    inference(subsumption_resolution,[],[f193,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t181_relat_1.p',dt_k5_relat_1)).

fof(f193,plain,(
    ! [X14,X17,X15,X13,X18,X16] :
      ( ~ r2_hidden(k4_tarski(X13,X14),X15)
      | ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | ~ r2_hidden(X14,k10_relat_1(X16,X17))
      | ~ v1_relat_1(k5_relat_1(X15,X16))
      | ~ r2_hidden(sK5(X16,X17,X14),X18)
      | r2_hidden(X13,k10_relat_1(k5_relat_1(X15,X16),X18)) ) ),
    inference(resolution,[],[f142,f45])).

fof(f45,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f142,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X4,X3)),k5_relat_1(X1,X0))
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X4)) ) ),
    inference(subsumption_resolution,[],[f141,f44])).

fof(f141,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X2,sK5(X0,X4,X3)),k5_relat_1(X1,X0))
      | ~ r2_hidden(X3,k10_relat_1(X0,X4)) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X2,sK5(X0,X4,X3)),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X4)) ) ),
    inference(resolution,[],[f48,f47])).

fof(f48,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t181_relat_1.p',d8_relat_1)).

fof(f585,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_7
    | ~ spl11_8 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f583,f86])).

fof(f86,plain,
    ( r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl11_8
  <=> r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(sK1,k10_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f583,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f582,f56])).

fof(f582,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f568,f63])).

fof(f568,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ spl11_7 ),
    inference(resolution,[],[f498,f83])).

fof(f83,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(k5_relat_1(sK1,sK2),sK0))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl11_7
  <=> ~ r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(k5_relat_1(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f251,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | spl11_11
    | ~ spl11_12 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f249,f56])).

fof(f249,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl11_2
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f248,f63])).

fof(f248,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f235,f101])).

fof(f101,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl11_11
  <=> ~ r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(sK1,k10_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f235,plain,
    ( r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl11_12 ),
    inference(resolution,[],[f210,f104])).

fof(f104,plain,
    ( r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl11_12
  <=> r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f210,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k10_relat_1(k5_relat_1(X2,X0),X3))
      | r2_hidden(X1,k10_relat_1(X2,k10_relat_1(X0,X3)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f209,f44])).

fof(f209,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(X1,k10_relat_1(X2,k10_relat_1(X0,X3)))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k10_relat_1(k5_relat_1(X2,X0),X3))
      | ~ v1_relat_1(k5_relat_1(X2,X0)) ) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(X1,k10_relat_1(X2,k10_relat_1(X0,X3)))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k10_relat_1(k5_relat_1(X2,X0),X3))
      | ~ v1_relat_1(k5_relat_1(X2,X0))
      | ~ r2_hidden(X1,k10_relat_1(k5_relat_1(X2,X0),X3)) ) ),
    inference(resolution,[],[f182,f46])).

fof(f182,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(k5_relat_1(X0,X1),X4,X2),X3)
      | ~ v1_relat_1(X1)
      | r2_hidden(X2,k10_relat_1(X0,k10_relat_1(X1,X3)))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k10_relat_1(k5_relat_1(X0,X1),X4)) ) ),
    inference(subsumption_resolution,[],[f174,f44])).

fof(f174,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(X2,k10_relat_1(X0,k10_relat_1(X1,X3)))
      | ~ r2_hidden(sK5(k5_relat_1(X0,X1),X4,X2),X3)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(X2,k10_relat_1(k5_relat_1(X0,X1),X4)) ) ),
    inference(resolution,[],[f173,f47])).

fof(f173,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,X3))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X3)
      | r2_hidden(X1,k10_relat_1(X0,k10_relat_1(X3,X4)))
      | ~ r2_hidden(X2,X4) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,X3))
      | ~ v1_relat_1(X3)
      | r2_hidden(X1,k10_relat_1(X0,k10_relat_1(X3,X4)))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,X3))
      | ~ r2_hidden(X2,X4)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f132,f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK9(X1,X0,X2,X3),k10_relat_1(X0,X4))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ r2_hidden(X3,X4)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f126,f44])).

fof(f126,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ r2_hidden(X3,X4)
      | r2_hidden(sK9(X1,X0,X2,X3),k10_relat_1(X0,X4)) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X4)
      | r2_hidden(sK9(X1,X0,X2,X3),k10_relat_1(X0,X4)) ) ),
    inference(resolution,[],[f49,f45])).

fof(f49,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X3,X4),X4),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK9(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f132,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK9(X1,X0,X2,X3),X4)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k10_relat_1(X1,X4)) ) ),
    inference(subsumption_resolution,[],[f131,f44])).

fof(f131,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ r2_hidden(sK9(X1,X0,X2,X3),X4)
      | r2_hidden(X2,k10_relat_1(X1,X4)) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(sK9(X1,X0,X2,X3),X4)
      | r2_hidden(X2,k10_relat_1(X1,X4)) ) ),
    inference(resolution,[],[f50,f45])).

fof(f50,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK9(X0,X1,X3,X4)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK9(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f247,plain,
    ( ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | spl11_9 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f245,f56])).

fof(f245,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f244,f63])).

fof(f244,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl11_6
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f234,f89])).

fof(f89,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl11_9
  <=> ~ r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(sK1,k10_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f234,plain,
    ( r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl11_6 ),
    inference(resolution,[],[f210,f80])).

fof(f80,plain,
    ( r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(k5_relat_1(sK1,sK2),sK0))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl11_6
  <=> r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(k5_relat_1(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f113,plain,
    ( spl11_5
    | spl11_11
    | spl11_13 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_11
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f111,f70])).

fof(f70,plain,
    ( k10_relat_1(k5_relat_1(sK1,sK2),sK0) != k10_relat_1(sK1,k10_relat_1(sK2,sK0))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl11_5
  <=> k10_relat_1(k5_relat_1(sK1,sK2),sK0) != k10_relat_1(sK1,k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f111,plain,
    ( k10_relat_1(k5_relat_1(sK1,sK2),sK0) = k10_relat_1(sK1,k10_relat_1(sK2,sK0))
    | ~ spl11_11
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f110,f101])).

fof(f110,plain,
    ( r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | k10_relat_1(k5_relat_1(sK1,sK2),sK0) = k10_relat_1(sK1,k10_relat_1(sK2,sK0))
    | ~ spl11_13 ),
    inference(resolution,[],[f107,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t181_relat_1.p',t2_tarski)).

fof(f108,plain,
    ( ~ spl11_11
    | ~ spl11_13
    | spl11_5 ),
    inference(avatar_split_clause,[],[f74,f69,f106,f100])).

fof(f74,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0))
    | ~ r2_hidden(sK3(k10_relat_1(sK1,k10_relat_1(sK2,sK0)),k10_relat_1(k5_relat_1(sK1,sK2),sK0)),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ spl11_5 ),
    inference(extensionality_resolution,[],[f31,f70])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,
    ( spl11_5
    | spl11_7
    | spl11_9 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f92,f70])).

fof(f92,plain,
    ( k10_relat_1(k5_relat_1(sK1,sK2),sK0) = k10_relat_1(sK1,k10_relat_1(sK2,sK0))
    | ~ spl11_7
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f91,f89])).

fof(f91,plain,
    ( r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | k10_relat_1(k5_relat_1(sK1,sK2),sK0) = k10_relat_1(sK1,k10_relat_1(sK2,sK0))
    | ~ spl11_7 ),
    inference(resolution,[],[f83,f30])).

fof(f90,plain,
    ( ~ spl11_7
    | ~ spl11_9
    | spl11_5 ),
    inference(avatar_split_clause,[],[f73,f69,f88,f82])).

fof(f73,plain,
    ( ~ r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(sK1,k10_relat_1(sK2,sK0)))
    | ~ r2_hidden(sK3(k10_relat_1(k5_relat_1(sK1,sK2),sK0),k10_relat_1(sK1,k10_relat_1(sK2,sK0))),k10_relat_1(k5_relat_1(sK1,sK2),sK0))
    | ~ spl11_5 ),
    inference(extensionality_resolution,[],[f31,f70])).

fof(f71,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    k10_relat_1(k5_relat_1(sK1,sK2),sK0) != k10_relat_1(sK1,k10_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) != k10_relat_1(k5_relat_1(X1,X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t181_relat_1.p',t181_relat_1)).

fof(f64,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
