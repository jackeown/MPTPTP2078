%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t160_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:53 EDT 2019

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 331 expanded)
%              Number of leaves         :   19 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  442 (1130 expanded)
%              Number of equality atoms :   27 ( 117 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4897,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f72,f79,f99,f104,f118,f122,f124,f126,f287,f317,f622,f626,f4892,f4896])).

fof(f4896,plain,
    ( ~ spl13_0
    | ~ spl13_2
    | ~ spl13_10
    | spl13_13 ),
    inference(avatar_contradiction_clause,[],[f4895])).

fof(f4895,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_10
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f4894,f117])).

fof(f117,plain,
    ( ~ r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl13_13
  <=> ~ r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f4894,plain,
    ( r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f4893,f71])).

fof(f71,plain,
    ( v1_relat_1(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl13_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f4893,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f4826,f64])).

fof(f64,plain,
    ( v1_relat_1(sK1)
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl13_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f4826,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_10 ),
    inference(resolution,[],[f4578,f108])).

fof(f108,plain,
    ( r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k9_relat_1(sK1,k2_relat_1(sK0)))
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl13_10
  <=> r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k9_relat_1(sK1,k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f4578,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(X4,k2_relat_1(X6)))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X6)
      | r2_hidden(X5,k2_relat_1(k5_relat_1(X6,X4))) ) ),
    inference(duplicate_literal_removal,[],[f4575])).

fof(f4575,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ r2_hidden(X5,k9_relat_1(X4,k2_relat_1(X6)))
      | ~ v1_relat_1(X6)
      | r2_hidden(X5,k2_relat_1(k5_relat_1(X6,X4)))
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X5,k9_relat_1(X4,k2_relat_1(X6))) ) ),
    inference(resolution,[],[f1374,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t160_relat_1.p',d13_relat_1)).

fof(f1374,plain,(
    ! [X50,X48,X51,X49] :
      ( ~ r2_hidden(sK7(X49,X51,X50),k2_relat_1(X48))
      | ~ v1_relat_1(X49)
      | ~ r2_hidden(X50,k9_relat_1(X49,X51))
      | ~ v1_relat_1(X48)
      | r2_hidden(X50,k2_relat_1(k5_relat_1(X48,X49))) ) ),
    inference(resolution,[],[f324,f52])).

fof(f52,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t160_relat_1.p',d5_relat_1)).

fof(f324,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK3(X1,sK7(X0,X2,X3)),X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X2))
      | ~ r2_hidden(sK7(X0,X2,X3),k2_relat_1(X1)) ) ),
    inference(resolution,[],[f190,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f190,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X10,sK7(X8,X11,X12)),X9)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | r2_hidden(k4_tarski(X10,X12),k5_relat_1(X9,X8))
      | ~ r2_hidden(X12,k9_relat_1(X8,X11)) ) ),
    inference(subsumption_resolution,[],[f187,f50])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t160_relat_1.p',dt_k5_relat_1)).

fof(f187,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(k5_relat_1(X9,X8))
      | ~ r2_hidden(k4_tarski(X10,sK7(X8,X11,X12)),X9)
      | ~ v1_relat_1(X9)
      | r2_hidden(k4_tarski(X10,X12),k5_relat_1(X9,X8))
      | ~ r2_hidden(X12,k9_relat_1(X8,X11)) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(k5_relat_1(X9,X8))
      | ~ r2_hidden(k4_tarski(X10,sK7(X8,X11,X12)),X9)
      | ~ v1_relat_1(X9)
      | r2_hidden(k4_tarski(X10,X12),k5_relat_1(X9,X8))
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(X12,k9_relat_1(X8,X11)) ) ),
    inference(resolution,[],[f56,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X3),X3),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

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
    file('/export/starexec/sandbox2/benchmark/relat_1__t160_relat_1.p',d8_relat_1)).

fof(f4892,plain,
    ( ~ spl13_0
    | ~ spl13_2
    | spl13_7
    | ~ spl13_8 ),
    inference(avatar_contradiction_clause,[],[f4891])).

fof(f4891,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_7
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f4890,f92])).

fof(f92,plain,
    ( ~ r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl13_7
  <=> ~ r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f4890,plain,
    ( r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f4889,f71])).

fof(f4889,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f4825,f64])).

fof(f4825,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_8 ),
    inference(resolution,[],[f4578,f95])).

fof(f95,plain,
    ( r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k9_relat_1(sK1,k2_relat_1(sK0)))
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl13_8
  <=> r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k9_relat_1(sK1,k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f626,plain,
    ( ~ spl13_0
    | ~ spl13_2
    | spl13_11
    | ~ spl13_12 ),
    inference(avatar_contradiction_clause,[],[f625])).

fof(f625,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_11
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f624,f114])).

fof(f114,plain,
    ( r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl13_12
  <=> r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f624,plain,
    ( ~ r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_11 ),
    inference(subsumption_resolution,[],[f623,f71])).

fof(f623,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_11 ),
    inference(subsumption_resolution,[],[f609,f64])).

fof(f609,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_11 ),
    inference(resolution,[],[f490,f111])).

fof(f111,plain,
    ( ~ r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k9_relat_1(sK1,k2_relat_1(sK0)))
    | ~ spl13_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl13_11
  <=> ~ r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k9_relat_1(sK1,k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f490,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X8,k9_relat_1(X7,k2_relat_1(X6)))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(X8,k2_relat_1(k5_relat_1(X6,X7))) ) ),
    inference(resolution,[],[f319,f51])).

fof(f319,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,X3))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X3)
      | r2_hidden(X2,k9_relat_1(X3,k2_relat_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f318])).

fof(f318,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,X3))
      | ~ v1_relat_1(X3)
      | r2_hidden(X2,k9_relat_1(X3,k2_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X0,X3))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f161,f171])).

fof(f171,plain,(
    ! [X6,X8,X7,X5] :
      ( r2_hidden(sK11(X6,X5,X7,X8),k2_relat_1(X6))
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X6,X5))
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f167,f50])).

fof(f167,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(k5_relat_1(X6,X5))
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X6,X5))
      | r2_hidden(sK11(X6,X5,X7,X8),k2_relat_1(X6)) ) ),
    inference(resolution,[],[f58,f52])).

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

fof(f161,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK11(X1,X0,X2,X3),X4)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k9_relat_1(X0,X4)) ) ),
    inference(subsumption_resolution,[],[f160,f50])).

fof(f160,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ r2_hidden(sK11(X1,X0,X2,X3),X4)
      | r2_hidden(X3,k9_relat_1(X0,X4)) ) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK11(X1,X0,X2,X3),X4)
      | r2_hidden(X3,k9_relat_1(X0,X4)) ) ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f622,plain,
    ( ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6
    | spl13_9 ),
    inference(avatar_contradiction_clause,[],[f621])).

fof(f621,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f620,f89])).

fof(f89,plain,
    ( r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl13_6
  <=> r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f620,plain,
    ( ~ r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f619,f71])).

fof(f619,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_0
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f608,f64])).

fof(f608,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_9 ),
    inference(resolution,[],[f490,f98])).

fof(f98,plain,
    ( ~ r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k9_relat_1(sK1,k2_relat_1(sK0)))
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl13_9
  <=> ~ r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k9_relat_1(sK1,k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f317,plain,
    ( spl13_16
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f273,f113,f70,f63,f315])).

fof(f315,plain,
    ( spl13_16
  <=> r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f273,plain,
    ( r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(sK1))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f272,f71])).

fof(f272,plain,
    ( r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl13_0
    | ~ spl13_12 ),
    inference(subsumption_resolution,[],[f264,f64])).

fof(f264,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl13_12 ),
    inference(resolution,[],[f224,f114])).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(k5_relat_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | r2_hidden(X2,k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f162,f51])).

fof(f162,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X6,X5))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X5)
      | r2_hidden(X8,k2_relat_1(X5)) ) ),
    inference(subsumption_resolution,[],[f155,f50])).

fof(f155,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(k5_relat_1(X6,X5))
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X6,X5))
      | r2_hidden(X8,k2_relat_1(X5)) ) ),
    inference(resolution,[],[f57,f52])).

fof(f287,plain,
    ( spl13_14
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f271,f88,f70,f63,f285])).

fof(f285,plain,
    ( spl13_14
  <=> r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f271,plain,
    ( r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(sK1))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f270,f71])).

fof(f270,plain,
    ( r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl13_0
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f263,f64])).

fof(f263,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl13_6 ),
    inference(resolution,[],[f224,f89])).

fof(f126,plain,
    ( spl13_12
    | spl13_5
    | spl13_11 ),
    inference(avatar_split_clause,[],[f123,f110,f77,f113])).

fof(f77,plain,
    ( spl13_5
  <=> k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f123,plain,
    ( r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_5
    | ~ spl13_11 ),
    inference(subsumption_resolution,[],[f119,f78])).

fof(f78,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f119,plain,
    ( r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t160_relat_1.p',t2_tarski)).

fof(f124,plain,
    ( spl13_6
    | spl13_5
    | spl13_9 ),
    inference(avatar_split_clause,[],[f105,f97,f77,f88])).

fof(f105,plain,
    ( r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_5
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f101,f78])).

fof(f101,plain,
    ( r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))
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
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))
    | ~ spl13_11
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f119,f117])).

fof(f118,plain,
    ( ~ spl13_11
    | ~ spl13_13
    | spl13_5 ),
    inference(avatar_split_clause,[],[f83,f77,f116,f110])).

fof(f83,plain,
    ( ~ r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r2_hidden(sK5(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))),k9_relat_1(sK1,k2_relat_1(sK0)))
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
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))
    | ~ spl13_7
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f101,f92])).

fof(f99,plain,
    ( ~ spl13_7
    | ~ spl13_9
    | spl13_5 ),
    inference(avatar_split_clause,[],[f82,f77,f97,f91])).

fof(f82,plain,
    ( ~ r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k9_relat_1(sK1,k2_relat_1(sK0)))
    | ~ r2_hidden(sK5(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl13_5 ),
    inference(extensionality_resolution,[],[f37,f78])).

fof(f79,plain,(
    ~ spl13_5 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t160_relat_1.p',t160_relat_1)).

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
