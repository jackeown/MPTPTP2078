%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t182_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:55 EDT 2019

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 331 expanded)
%              Number of leaves         :   19 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  441 (1128 expanded)
%              Number of equality atoms :   27 ( 117 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5014,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f72,f79,f99,f104,f118,f122,f124,f126,f288,f325,f649,f653,f5007,f5011])).

fof(f5011,plain,
    ( ~ spl13_0
    | ~ spl13_2
    | ~ spl13_10
    | spl13_13 ),
    inference(avatar_contradiction_clause,[],[f5010])).

fof(f5010,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_10
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f5009,f64])).

fof(f64,plain,
    ( v1_relat_1(sK1)
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl13_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f5009,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl13_2
    | ~ spl13_10
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f5008,f117])).

fof(f117,plain,
    ( ~ r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl13_13
  <=> ~ r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f5008,plain,
    ( r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl13_2
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f4907,f71])).

fof(f71,plain,
    ( v1_relat_1(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl13_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f4907,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl13_10 ),
    inference(resolution,[],[f4663,f108])).

fof(f108,plain,
    ( r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl13_10
  <=> r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f4663,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X16,k10_relat_1(X15,k1_relat_1(X14)))
      | ~ v1_relat_1(X15)
      | r2_hidden(X16,k1_relat_1(k5_relat_1(X15,X14)))
      | ~ v1_relat_1(X14) ) ),
    inference(duplicate_literal_removal,[],[f4662])).

fof(f4662,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | r2_hidden(X16,k1_relat_1(k5_relat_1(X15,X14)))
      | ~ r2_hidden(X16,k10_relat_1(X15,k1_relat_1(X14)))
      | ~ v1_relat_1(X15)
      | ~ r2_hidden(X16,k10_relat_1(X15,k1_relat_1(X14))) ) ),
    inference(resolution,[],[f974,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t182_relat_1.p',d14_relat_1)).

fof(f974,plain,(
    ! [X30,X31,X29,X32] :
      ( ~ r2_hidden(sK7(X29,X31,X32),k1_relat_1(X30))
      | ~ v1_relat_1(X30)
      | ~ v1_relat_1(X29)
      | r2_hidden(X32,k1_relat_1(k5_relat_1(X29,X30)))
      | ~ r2_hidden(X32,k10_relat_1(X29,X31)) ) ),
    inference(duplicate_literal_removal,[],[f936])).

fof(f936,plain,(
    ! [X30,X31,X29,X32] :
      ( ~ v1_relat_1(X29)
      | ~ v1_relat_1(X30)
      | ~ r2_hidden(sK7(X29,X31,X32),k1_relat_1(X30))
      | r2_hidden(X32,k1_relat_1(k5_relat_1(X29,X30)))
      | ~ v1_relat_1(X29)
      | ~ r2_hidden(X32,k10_relat_1(X29,X31)) ) ),
    inference(resolution,[],[f299,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK7(X0,X1,X3)),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,sK7(X0,X1,X3)),X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f299,plain,(
    ! [X21,X19,X22,X20] :
      ( ~ r2_hidden(k4_tarski(X19,X20),X21)
      | ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | ~ r2_hidden(X20,k1_relat_1(X22))
      | r2_hidden(X19,k1_relat_1(k5_relat_1(X21,X22))) ) ),
    inference(resolution,[],[f190,f52])).

fof(f52,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t182_relat_1.p',d4_relat_1)).

fof(f190,plain,(
    ! [X12,X10,X11,X9] :
      ( r2_hidden(k4_tarski(X11,sK3(X9,X12)),k5_relat_1(X10,X9))
      | ~ r2_hidden(k4_tarski(X11,X12),X10)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X9)
      | ~ r2_hidden(X12,k1_relat_1(X9)) ) ),
    inference(subsumption_resolution,[],[f180,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t182_relat_1.p',dt_k5_relat_1)).

fof(f180,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(k5_relat_1(X10,X9))
      | ~ r2_hidden(k4_tarski(X11,X12),X10)
      | ~ v1_relat_1(X10)
      | r2_hidden(k4_tarski(X11,sK3(X9,X12)),k5_relat_1(X10,X9))
      | ~ r2_hidden(X12,k1_relat_1(X9)) ) ),
    inference(resolution,[],[f56,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t182_relat_1.p',d8_relat_1)).

fof(f5007,plain,
    ( ~ spl13_0
    | ~ spl13_2
    | spl13_7
    | ~ spl13_8 ),
    inference(avatar_contradiction_clause,[],[f5006])).

fof(f5006,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_7
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f5005,f64])).

fof(f5005,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl13_2
    | ~ spl13_7
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f5004,f92])).

fof(f92,plain,
    ( ~ r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl13_7
  <=> ~ r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f5004,plain,
    ( r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl13_2
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f4906,f71])).

fof(f4906,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl13_8 ),
    inference(resolution,[],[f4663,f95])).

fof(f95,plain,
    ( r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl13_8
  <=> r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f653,plain,
    ( ~ spl13_0
    | ~ spl13_2
    | spl13_11
    | ~ spl13_12 ),
    inference(avatar_contradiction_clause,[],[f652])).

fof(f652,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_11
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f651,f114])).

fof(f114,plain,
    ( r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl13_12
  <=> r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f651,plain,
    ( ~ r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_11 ),
    inference(subsumption_resolution,[],[f650,f71])).

fof(f650,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_11 ),
    inference(subsumption_resolution,[],[f636,f64])).

fof(f636,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_11 ),
    inference(resolution,[],[f507,f111])).

fof(f111,plain,
    ( ~ r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl13_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl13_11
  <=> ~ r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f507,plain,(
    ! [X37,X35,X36] :
      ( r2_hidden(X37,k10_relat_1(X35,k1_relat_1(X36)))
      | ~ v1_relat_1(X36)
      | ~ v1_relat_1(X35)
      | ~ r2_hidden(X37,k1_relat_1(k5_relat_1(X35,X36))) ) ),
    inference(resolution,[],[f331,f51])).

fof(f331,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,X3))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X3)
      | r2_hidden(X1,k10_relat_1(X0,k1_relat_1(X3))) ) ),
    inference(duplicate_literal_removal,[],[f328])).

fof(f328,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,X3))
      | ~ v1_relat_1(X3)
      | r2_hidden(X1,k10_relat_1(X0,k1_relat_1(X3)))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,X3))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f168,f159])).

fof(f159,plain,(
    ! [X6,X8,X7,X5] :
      ( r2_hidden(sK11(X6,X5,X7,X8),k1_relat_1(X5))
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X6,X5))
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f155,f50])).

fof(f155,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(k5_relat_1(X6,X5))
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X6,X5))
      | r2_hidden(sK11(X6,X5,X7,X8),k1_relat_1(X5)) ) ),
    inference(resolution,[],[f57,f52])).

fof(f57,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X1,X3,X4),X4),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK11(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f168,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK11(X1,X0,X2,X3),X4)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k10_relat_1(X1,X4)) ) ),
    inference(subsumption_resolution,[],[f167,f50])).

fof(f167,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ r2_hidden(sK11(X1,X0,X2,X3),X4)
      | r2_hidden(X2,k10_relat_1(X1,X4)) ) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(sK11(X1,X0,X2,X3),X4)
      | r2_hidden(X2,k10_relat_1(X1,X4)) ) ),
    inference(resolution,[],[f58,f53])).

fof(f53,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK11(X0,X1,X3,X4)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK11(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f649,plain,
    ( ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6
    | spl13_9 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f647,f89])).

fof(f89,plain,
    ( r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl13_6
  <=> r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f647,plain,
    ( ~ r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f646,f71])).

fof(f646,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f635,f64])).

fof(f635,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_9 ),
    inference(resolution,[],[f507,f98])).

fof(f98,plain,
    ( ~ r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl13_9
  <=> ~ r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f325,plain,
    ( spl13_16
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f271,f113,f70,f63,f323])).

fof(f323,plain,
    ( spl13_16
  <=> r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f271,plain,
    ( r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK0))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f270,f71])).

fof(f270,plain,
    ( r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl13_0
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f250,f64])).

fof(f250,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl13_12 ),
    inference(resolution,[],[f227,f114])).

fof(f227,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(X13,k1_relat_1(k5_relat_1(X11,X12)))
      | ~ v1_relat_1(X12)
      | r2_hidden(X13,k1_relat_1(X11))
      | ~ v1_relat_1(X11) ) ),
    inference(resolution,[],[f169,f51])).

fof(f169,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X6,X5))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X5)
      | r2_hidden(X7,k1_relat_1(X6)) ) ),
    inference(subsumption_resolution,[],[f162,f50])).

fof(f162,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(k5_relat_1(X6,X5))
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X6,X5))
      | r2_hidden(X7,k1_relat_1(X6)) ) ),
    inference(resolution,[],[f58,f52])).

fof(f288,plain,
    ( spl13_14
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f269,f88,f70,f63,f286])).

fof(f286,plain,
    ( spl13_14
  <=> r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f269,plain,
    ( r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(sK0))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f268,f71])).

fof(f268,plain,
    ( r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl13_0
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f249,f64])).

fof(f249,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl13_6 ),
    inference(resolution,[],[f227,f89])).

fof(f126,plain,
    ( spl13_12
    | spl13_5
    | spl13_11 ),
    inference(avatar_split_clause,[],[f123,f110,f77,f113])).

fof(f77,plain,
    ( spl13_5
  <=> k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f123,plain,
    ( r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_5
    | ~ spl13_11 ),
    inference(subsumption_resolution,[],[f119,f78])).

fof(f78,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f119,plain,
    ( r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ spl13_11 ),
    inference(resolution,[],[f111,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t182_relat_1.p',t2_tarski)).

fof(f124,plain,
    ( spl13_6
    | spl13_5
    | spl13_9 ),
    inference(avatar_split_clause,[],[f105,f97,f77,f88])).

fof(f105,plain,
    ( r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_5
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f101,f78])).

fof(f101,plain,
    ( r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ spl13_9 ),
    inference(resolution,[],[f98,f36])).

fof(f122,plain,
    ( spl13_5
    | spl13_11
    | spl13_13 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl13_5
    | ~ spl13_11
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f120,f78])).

fof(f120,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ spl13_11
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f119,f117])).

fof(f118,plain,
    ( ~ spl13_11
    | ~ spl13_13
    | spl13_5 ),
    inference(avatar_split_clause,[],[f83,f77,f116,f110])).

fof(f83,plain,
    ( ~ r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r2_hidden(sK5(k10_relat_1(sK0,k1_relat_1(sK1)),k1_relat_1(k5_relat_1(sK0,sK1))),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl13_5 ),
    inference(extensionality_resolution,[],[f37,f78])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f104,plain,
    ( spl13_5
    | spl13_7
    | spl13_9 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl13_5
    | ~ spl13_7
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f102,f78])).

fof(f102,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ spl13_7
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f101,f92])).

fof(f99,plain,
    ( ~ spl13_7
    | ~ spl13_9
    | spl13_5 ),
    inference(avatar_split_clause,[],[f82,f77,f97,f91])).

fof(f82,plain,
    ( ~ r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ r2_hidden(sK5(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_5 ),
    inference(extensionality_resolution,[],[f37,f78])).

fof(f79,plain,(
    ~ spl13_5 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t182_relat_1.p',t182_relat_1)).

fof(f72,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    spl13_0 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
