%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0467+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:02 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 295 expanded)
%              Number of leaves         :    7 (  63 expanded)
%              Depth                    :   49
%              Number of atoms          :  636 (1850 expanded)
%              Number of equality atoms :   71 ( 203 expanded)
%              Maximal formula depth    :   24 (  12 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f904,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f903])).

fof(f903,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f898])).

fof(f898,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f31,f36,f26,f41,f897])).

fof(f897,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f896,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f896,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f895,f19])).

fof(f895,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k5_relat_1(X2,X0))
      | ~ v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f894])).

fof(f894,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k5_relat_1(X2,X0))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f890,f19])).

fof(f890,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(k5_relat_1(X4,k5_relat_1(X5,X6)))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | k5_relat_1(k5_relat_1(X4,X5),X6) = k5_relat_1(X4,k5_relat_1(X5,X6))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k5_relat_1(X4,X5)) ) ),
    inference(duplicate_literal_removal,[],[f883])).

fof(f883,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | k5_relat_1(k5_relat_1(X4,X5),X6) = k5_relat_1(X4,k5_relat_1(X5,X6))
      | ~ v1_relat_1(k5_relat_1(X4,k5_relat_1(X5,X6)))
      | ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,X5),X6) = k5_relat_1(X4,k5_relat_1(X5,X6))
      | ~ v1_relat_1(k5_relat_1(X4,k5_relat_1(X5,X6)))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(k5_relat_1(X4,X5))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f881,f599])).

fof(f599,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(k4_tarski(sK3(k5_relat_1(X9,X10),X11,k5_relat_1(X9,k5_relat_1(X10,X11))),sK4(k5_relat_1(X9,X10),X11,k5_relat_1(X9,k5_relat_1(X10,X11)))),k5_relat_1(X9,k5_relat_1(X10,X11)))
      | ~ v1_relat_1(X10)
      | k5_relat_1(X9,k5_relat_1(X10,X11)) = k5_relat_1(k5_relat_1(X9,X10),X11)
      | ~ v1_relat_1(k5_relat_1(X9,k5_relat_1(X10,X11)))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(k5_relat_1(X9,X10))
      | ~ v1_relat_1(X9) ) ),
    inference(subsumption_resolution,[],[f596,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f596,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(X9,X10),X11,k5_relat_1(X9,k5_relat_1(X10,X11))),sK4(k5_relat_1(X9,X10),X11,k5_relat_1(X9,k5_relat_1(X10,X11)))),X11)
      | k5_relat_1(X9,k5_relat_1(X10,X11)) = k5_relat_1(k5_relat_1(X9,X10),X11)
      | ~ v1_relat_1(k5_relat_1(X9,k5_relat_1(X10,X11)))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(k5_relat_1(X9,X10))
      | r2_hidden(k4_tarski(sK3(k5_relat_1(X9,X10),X11,k5_relat_1(X9,k5_relat_1(X10,X11))),sK4(k5_relat_1(X9,X10),X11,k5_relat_1(X9,k5_relat_1(X10,X11)))),k5_relat_1(X9,k5_relat_1(X10,X11))) ) ),
    inference(duplicate_literal_removal,[],[f593])).

fof(f593,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(X9,X10),X11,k5_relat_1(X9,k5_relat_1(X10,X11))),sK4(k5_relat_1(X9,X10),X11,k5_relat_1(X9,k5_relat_1(X10,X11)))),X11)
      | k5_relat_1(X9,k5_relat_1(X10,X11)) = k5_relat_1(k5_relat_1(X9,X10),X11)
      | ~ v1_relat_1(k5_relat_1(X9,k5_relat_1(X10,X11)))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(k5_relat_1(X9,X10))
      | r2_hidden(k4_tarski(sK3(k5_relat_1(X9,X10),X11,k5_relat_1(X9,k5_relat_1(X10,X11))),sK4(k5_relat_1(X9,X10),X11,k5_relat_1(X9,k5_relat_1(X10,X11)))),k5_relat_1(X9,k5_relat_1(X10,X11)))
      | ~ v1_relat_1(k5_relat_1(X9,k5_relat_1(X10,X11)))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(k5_relat_1(X9,X10))
      | k5_relat_1(X9,k5_relat_1(X10,X11)) = k5_relat_1(k5_relat_1(X9,X10),X11) ) ),
    inference(resolution,[],[f590,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK6(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f590,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13))),X14),k5_relat_1(X11,X12))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ r2_hidden(k4_tarski(X14,sK4(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13)))),X13)
      | k5_relat_1(k5_relat_1(X11,X12),X13) = k5_relat_1(X11,k5_relat_1(X12,X13))
      | ~ v1_relat_1(k5_relat_1(X11,k5_relat_1(X12,X13)))
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(k5_relat_1(X11,X12)) ) ),
    inference(subsumption_resolution,[],[f589,f13])).

fof(f13,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f589,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13))),X14),k5_relat_1(X11,X12))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ r2_hidden(k4_tarski(X14,sK4(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13)))),X13)
      | k5_relat_1(k5_relat_1(X11,X12),X13) = k5_relat_1(X11,k5_relat_1(X12,X13))
      | ~ v1_relat_1(k5_relat_1(X11,k5_relat_1(X12,X13)))
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(k5_relat_1(X11,X12))
      | r2_hidden(k4_tarski(sK3(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13))),sK4(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13)))),k5_relat_1(X11,k5_relat_1(X12,X13))) ) ),
    inference(subsumption_resolution,[],[f586,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK6(X2,X0,X1),sK4(X2,X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK3(X2,X0,X1),X3),X2)
      | ~ r2_hidden(k4_tarski(X3,sK4(X2,X0,X1)),X0)
      | ~ v1_relat_1(X2)
      | k5_relat_1(X2,X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK3(X2,X0,X1),X3),X2)
      | ~ r2_hidden(k4_tarski(X3,sK4(X2,X0,X1)),X0)
      | ~ v1_relat_1(X2)
      | k5_relat_1(X2,X0) = X1
      | r2_hidden(k4_tarski(sK6(X2,X0,X1),sK4(X2,X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | k5_relat_1(X2,X0) = X1 ) ),
    inference(resolution,[],[f13,f15])).

fof(f586,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13))),X14),k5_relat_1(X11,X12))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ r2_hidden(k4_tarski(X14,sK4(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13)))),X13)
      | k5_relat_1(k5_relat_1(X11,X12),X13) = k5_relat_1(X11,k5_relat_1(X12,X13))
      | ~ v1_relat_1(k5_relat_1(X11,k5_relat_1(X12,X13)))
      | ~ v1_relat_1(X13)
      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13))),sK4(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13)))),X13)
      | ~ v1_relat_1(k5_relat_1(X11,X12))
      | r2_hidden(k4_tarski(sK3(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13))),sK4(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13)))),k5_relat_1(X11,k5_relat_1(X12,X13))) ) ),
    inference(duplicate_literal_removal,[],[f583])).

fof(f583,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13))),X14),k5_relat_1(X11,X12))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ r2_hidden(k4_tarski(X14,sK4(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13)))),X13)
      | k5_relat_1(k5_relat_1(X11,X12),X13) = k5_relat_1(X11,k5_relat_1(X12,X13))
      | ~ v1_relat_1(k5_relat_1(X11,k5_relat_1(X12,X13)))
      | ~ v1_relat_1(X13)
      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13))),sK4(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13)))),X13)
      | ~ v1_relat_1(k5_relat_1(X11,X12))
      | r2_hidden(k4_tarski(sK3(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13))),sK4(k5_relat_1(X11,X12),X13,k5_relat_1(X11,k5_relat_1(X12,X13)))),k5_relat_1(X11,k5_relat_1(X12,X13)))
      | ~ v1_relat_1(k5_relat_1(X11,k5_relat_1(X12,X13)))
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(k5_relat_1(X11,X12))
      | k5_relat_1(k5_relat_1(X11,X12),X13) = k5_relat_1(X11,k5_relat_1(X12,X13)) ) ),
    inference(resolution,[],[f577,f14])).

fof(f577,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),X10),k5_relat_1(X7,X8))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),X9),k5_relat_1(X7,X8))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(k4_tarski(X9,sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),X6)
      | k5_relat_1(X7,k5_relat_1(X8,X6)) = k5_relat_1(k5_relat_1(X7,X8),X6)
      | ~ v1_relat_1(k5_relat_1(X7,k5_relat_1(X8,X6)))
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X10,sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),X6)
      | ~ v1_relat_1(k5_relat_1(X7,X8)) ) ),
    inference(subsumption_resolution,[],[f575,f13])).

fof(f575,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),X9),k5_relat_1(X7,X8))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(k4_tarski(X9,sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),X6)
      | k5_relat_1(X7,k5_relat_1(X8,X6)) = k5_relat_1(k5_relat_1(X7,X8),X6)
      | ~ v1_relat_1(k5_relat_1(X7,k5_relat_1(X8,X6)))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),X10),k5_relat_1(X7,X8))
      | ~ r2_hidden(k4_tarski(X10,sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),X6)
      | r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),k5_relat_1(X7,k5_relat_1(X8,X6)))
      | ~ v1_relat_1(k5_relat_1(X7,X8)) ) ),
    inference(duplicate_literal_removal,[],[f572])).

fof(f572,plain,(
    ! [X6,X10,X8,X7,X9] :
      ( ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),X9),k5_relat_1(X7,X8))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X9,sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),X6)
      | k5_relat_1(X7,k5_relat_1(X8,X6)) = k5_relat_1(k5_relat_1(X7,X8),X6)
      | ~ v1_relat_1(k5_relat_1(X7,k5_relat_1(X8,X6)))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),X10),k5_relat_1(X7,X8))
      | ~ r2_hidden(k4_tarski(X10,sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),X6)
      | r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),k5_relat_1(X7,k5_relat_1(X8,X6)))
      | ~ v1_relat_1(k5_relat_1(X7,k5_relat_1(X8,X6)))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(k5_relat_1(X7,X8))
      | k5_relat_1(X7,k5_relat_1(X8,X6)) = k5_relat_1(k5_relat_1(X7,X8),X6) ) ),
    inference(resolution,[],[f136,f15])).

fof(f136,plain,(
    ! [X12,X10,X8,X13,X11,X9] :
      ( ~ r2_hidden(k4_tarski(sK6(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11))),sK4(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11)))),X11)
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11))),X12),k5_relat_1(X8,X9))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X11)
      | ~ r2_hidden(k4_tarski(X12,sK4(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11)))),X10)
      | k5_relat_1(k5_relat_1(X8,X9),X10) = k5_relat_1(X8,k5_relat_1(X9,X11))
      | ~ v1_relat_1(k5_relat_1(X8,k5_relat_1(X9,X11)))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11))),X13),k5_relat_1(X8,X9))
      | ~ r2_hidden(k4_tarski(X13,sK4(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11)))),X10) ) ),
    inference(subsumption_resolution,[],[f133,f19])).

fof(f133,plain,(
    ! [X12,X10,X8,X13,X11,X9] :
      ( k5_relat_1(k5_relat_1(X8,X9),X10) = k5_relat_1(X8,k5_relat_1(X9,X11))
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11))),X12),k5_relat_1(X8,X9))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(k5_relat_1(X8,X9))
      | ~ v1_relat_1(X11)
      | ~ r2_hidden(k4_tarski(X12,sK4(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11)))),X10)
      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11))),sK4(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11)))),X11)
      | ~ v1_relat_1(k5_relat_1(X8,k5_relat_1(X9,X11)))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11))),X13),k5_relat_1(X8,X9))
      | ~ r2_hidden(k4_tarski(X13,sK4(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11)))),X10) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X12,X10,X8,X13,X11,X9] :
      ( k5_relat_1(k5_relat_1(X8,X9),X10) = k5_relat_1(X8,k5_relat_1(X9,X11))
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11))),X12),k5_relat_1(X8,X9))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(k5_relat_1(X8,X9))
      | ~ v1_relat_1(X11)
      | ~ r2_hidden(k4_tarski(X12,sK4(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11)))),X10)
      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11))),sK4(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11)))),X11)
      | ~ v1_relat_1(k5_relat_1(X8,k5_relat_1(X9,X11)))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11))),X13),k5_relat_1(X8,X9))
      | ~ r2_hidden(k4_tarski(X13,sK4(k5_relat_1(X8,X9),X10,k5_relat_1(X8,k5_relat_1(X9,X11)))),X10)
      | ~ v1_relat_1(k5_relat_1(X8,X9))
      | k5_relat_1(k5_relat_1(X8,X9),X10) = k5_relat_1(X8,k5_relat_1(X9,X11))
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f125,f47])).

fof(f47,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(k4_tarski(sK3(X6,X4,X5),sK6(X6,X4,X5)),X6)
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(k4_tarski(sK3(X6,X4,X5),X7),X6)
      | ~ r2_hidden(k4_tarski(X7,sK4(X6,X4,X5)),X4)
      | ~ v1_relat_1(X6)
      | k5_relat_1(X6,X4) = X5
      | ~ v1_relat_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(k4_tarski(sK3(X6,X4,X5),X7),X6)
      | ~ r2_hidden(k4_tarski(X7,sK4(X6,X4,X5)),X4)
      | ~ v1_relat_1(X6)
      | k5_relat_1(X6,X4) = X5
      | r2_hidden(k4_tarski(sK3(X6,X4,X5),sK6(X6,X4,X5)),X6)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X6)
      | k5_relat_1(X6,X4) = X5 ) ),
    inference(resolution,[],[f13,f14])).

fof(f125,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4))),X6),k5_relat_1(X2,X3))
      | k5_relat_1(X0,X1) = k5_relat_1(X2,k5_relat_1(X3,X4))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4))),X5),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4)))),X1)
      | ~ r2_hidden(k4_tarski(X6,sK4(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4)))),X4) ) ),
    inference(subsumption_resolution,[],[f124,f19])).

fof(f124,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,X1) = k5_relat_1(X2,k5_relat_1(X3,X4))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4))),X5),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4))),X6),k5_relat_1(X2,X3))
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4)))),X1)
      | ~ r2_hidden(k4_tarski(X6,sK4(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4)))),X4)
      | ~ v1_relat_1(k5_relat_1(X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,X1) = k5_relat_1(X2,k5_relat_1(X3,X4))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4))),X5),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4))),X6),k5_relat_1(X2,X3))
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4)))),X1)
      | ~ r2_hidden(k4_tarski(X6,sK4(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4)))),X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,k5_relat_1(X2,k5_relat_1(X3,X4))),X6),k5_relat_1(X2,X3)) ) ),
    inference(resolution,[],[f94,f21])).

fof(f21,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f94,plain,(
    ! [X6,X12,X10,X8,X7,X5,X13,X11,X9] :
      ( ~ r2_hidden(k4_tarski(sK5(X8,X11,sK3(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10))),X12),X13),X9)
      | ~ v1_relat_1(X6)
      | k5_relat_1(X6,X7) = k5_relat_1(X8,k5_relat_1(X9,X10))
      | ~ v1_relat_1(X7)
      | ~ r2_hidden(k4_tarski(sK3(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10))),X5),X6)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X11)
      | ~ r2_hidden(k4_tarski(sK3(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10))),X12),k5_relat_1(X8,X11))
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(X5,sK4(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10)))),X7)
      | ~ r2_hidden(k4_tarski(X13,sK4(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10)))),X10)
      | ~ v1_relat_1(X9) ) ),
    inference(subsumption_resolution,[],[f92,f19])).

fof(f92,plain,(
    ! [X6,X12,X10,X8,X7,X5,X13,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X5,sK4(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10)))),X7)
      | ~ v1_relat_1(X6)
      | k5_relat_1(X6,X7) = k5_relat_1(X8,k5_relat_1(X9,X10))
      | ~ v1_relat_1(k5_relat_1(X9,X10))
      | ~ v1_relat_1(X7)
      | ~ r2_hidden(k4_tarski(sK3(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10))),X5),X6)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X11)
      | ~ r2_hidden(k4_tarski(sK3(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10))),X12),k5_relat_1(X8,X11))
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(sK5(X8,X11,sK3(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10))),X12),X13),X9)
      | ~ r2_hidden(k4_tarski(X13,sK4(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10)))),X10)
      | ~ v1_relat_1(X9) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X6,X12,X10,X8,X7,X5,X13,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X5,sK4(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10)))),X7)
      | ~ v1_relat_1(X6)
      | k5_relat_1(X6,X7) = k5_relat_1(X8,k5_relat_1(X9,X10))
      | ~ v1_relat_1(k5_relat_1(X9,X10))
      | ~ v1_relat_1(X7)
      | ~ r2_hidden(k4_tarski(sK3(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10))),X5),X6)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X11)
      | ~ r2_hidden(k4_tarski(sK3(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10))),X12),k5_relat_1(X8,X11))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(k5_relat_1(X9,X10))
      | ~ r2_hidden(k4_tarski(sK5(X8,X11,sK3(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10))),X12),X13),X9)
      | ~ r2_hidden(k4_tarski(X13,sK4(X6,X7,k5_relat_1(X8,k5_relat_1(X9,X10)))),X10)
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f61,f20])).

fof(f20,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X14,X12,X10,X15,X13,X11,X9] :
      ( ~ r2_hidden(k4_tarski(sK5(X11,X14,sK3(X9,X10,k5_relat_1(X11,X12)),X15),sK4(X9,X10,k5_relat_1(X11,X12))),X12)
      | ~ r2_hidden(k4_tarski(X13,sK4(X9,X10,k5_relat_1(X11,X12))),X10)
      | ~ v1_relat_1(X9)
      | k5_relat_1(X9,X10) = k5_relat_1(X11,X12)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(sK3(X9,X10,k5_relat_1(X11,X12)),X13),X9)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X14)
      | ~ r2_hidden(k4_tarski(sK3(X9,X10,k5_relat_1(X11,X12)),X15),k5_relat_1(X11,X14)) ) ),
    inference(subsumption_resolution,[],[f55,f19])).

fof(f55,plain,(
    ! [X14,X12,X10,X15,X13,X11,X9] :
      ( ~ r2_hidden(k4_tarski(sK3(X9,X10,k5_relat_1(X11,X12)),X13),X9)
      | ~ r2_hidden(k4_tarski(X13,sK4(X9,X10,k5_relat_1(X11,X12))),X10)
      | ~ v1_relat_1(X9)
      | k5_relat_1(X9,X10) = k5_relat_1(X11,X12)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(sK5(X11,X14,sK3(X9,X10,k5_relat_1(X11,X12)),X15),sK4(X9,X10,k5_relat_1(X11,X12))),X12)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X14)
      | ~ v1_relat_1(k5_relat_1(X11,X14))
      | ~ r2_hidden(k4_tarski(sK3(X9,X10,k5_relat_1(X11,X12)),X15),k5_relat_1(X11,X14)) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X14,X12,X10,X15,X13,X11,X9] :
      ( ~ r2_hidden(k4_tarski(sK3(X9,X10,k5_relat_1(X11,X12)),X13),X9)
      | ~ r2_hidden(k4_tarski(X13,sK4(X9,X10,k5_relat_1(X11,X12))),X10)
      | ~ v1_relat_1(X9)
      | k5_relat_1(X9,X10) = k5_relat_1(X11,X12)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(sK5(X11,X14,sK3(X9,X10,k5_relat_1(X11,X12)),X15),sK4(X9,X10,k5_relat_1(X11,X12))),X12)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X14)
      | ~ v1_relat_1(k5_relat_1(X11,X14))
      | ~ v1_relat_1(X11)
      | ~ r2_hidden(k4_tarski(sK3(X9,X10,k5_relat_1(X11,X12)),X15),k5_relat_1(X11,X14)) ) ),
    inference(resolution,[],[f49,f22])).

fof(f22,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X12,X10,X8,X13,X11,X9] :
      ( ~ r2_hidden(k4_tarski(sK3(X11,X8,k5_relat_1(X9,X10)),X13),X9)
      | ~ r2_hidden(k4_tarski(sK3(X11,X8,k5_relat_1(X9,X10)),X12),X11)
      | ~ r2_hidden(k4_tarski(X12,sK4(X11,X8,k5_relat_1(X9,X10))),X8)
      | ~ v1_relat_1(X11)
      | k5_relat_1(X9,X10) = k5_relat_1(X11,X8)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(k4_tarski(X13,sK4(X11,X8,k5_relat_1(X9,X10))),X10)
      | ~ v1_relat_1(X9) ) ),
    inference(subsumption_resolution,[],[f46,f19])).

fof(f46,plain,(
    ! [X12,X10,X8,X13,X11,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(k5_relat_1(X9,X10))
      | ~ r2_hidden(k4_tarski(sK3(X11,X8,k5_relat_1(X9,X10)),X12),X11)
      | ~ r2_hidden(k4_tarski(X12,sK4(X11,X8,k5_relat_1(X9,X10))),X8)
      | ~ v1_relat_1(X11)
      | k5_relat_1(X9,X10) = k5_relat_1(X11,X8)
      | ~ v1_relat_1(X10)
      | ~ r2_hidden(k4_tarski(sK3(X11,X8,k5_relat_1(X9,X10)),X13),X9)
      | ~ r2_hidden(k4_tarski(X13,sK4(X11,X8,k5_relat_1(X9,X10))),X10)
      | ~ v1_relat_1(X9) ) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X12,X10,X8,X13,X11,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(k5_relat_1(X9,X10))
      | ~ r2_hidden(k4_tarski(sK3(X11,X8,k5_relat_1(X9,X10)),X12),X11)
      | ~ r2_hidden(k4_tarski(X12,sK4(X11,X8,k5_relat_1(X9,X10))),X8)
      | ~ v1_relat_1(X11)
      | k5_relat_1(X9,X10) = k5_relat_1(X11,X8)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(k5_relat_1(X9,X10))
      | ~ r2_hidden(k4_tarski(sK3(X11,X8,k5_relat_1(X9,X10)),X13),X9)
      | ~ r2_hidden(k4_tarski(X13,sK4(X11,X8,k5_relat_1(X9,X10))),X10)
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f13,f20])).

fof(f881,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),k5_relat_1(X7,k5_relat_1(X8,X6)))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X6)
      | k5_relat_1(X7,k5_relat_1(X8,X6)) = k5_relat_1(k5_relat_1(X7,X8),X6)
      | ~ v1_relat_1(k5_relat_1(X7,k5_relat_1(X8,X6))) ) ),
    inference(subsumption_resolution,[],[f878,f19])).

fof(f878,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(k5_relat_1(X8,X6))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),k5_relat_1(X7,k5_relat_1(X8,X6)))
      | k5_relat_1(X7,k5_relat_1(X8,X6)) = k5_relat_1(k5_relat_1(X7,X8),X6)
      | ~ v1_relat_1(k5_relat_1(X7,k5_relat_1(X8,X6))) ) ),
    inference(duplicate_literal_removal,[],[f877])).

fof(f877,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(k5_relat_1(X8,X6))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),k5_relat_1(X7,k5_relat_1(X8,X6)))
      | k5_relat_1(X7,k5_relat_1(X8,X6)) = k5_relat_1(k5_relat_1(X7,X8),X6)
      | ~ v1_relat_1(k5_relat_1(X8,X6))
      | ~ v1_relat_1(k5_relat_1(X7,k5_relat_1(X8,X6)))
      | ~ v1_relat_1(X7)
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6))),sK4(k5_relat_1(X7,X8),X6,k5_relat_1(X7,k5_relat_1(X8,X6)))),k5_relat_1(X7,k5_relat_1(X8,X6))) ) ),
    inference(resolution,[],[f865,f21])).

fof(f865,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK5(X0,X3,sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),sK4(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2)))),k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),k5_relat_1(X0,X3))
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f864,f19])).

fof(f864,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),k5_relat_1(X0,X3))
      | ~ v1_relat_1(k5_relat_1(X1,X2))
      | ~ r2_hidden(k4_tarski(sK5(X0,X3,sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),sK4(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2)))),k5_relat_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f863,f19])).

fof(f863,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X0,X3))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),k5_relat_1(X0,X3))
      | ~ v1_relat_1(k5_relat_1(X1,X2))
      | ~ r2_hidden(k4_tarski(sK5(X0,X3,sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),sK4(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2)))),k5_relat_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f862,f19])).

fof(f862,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X0,X3))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),k5_relat_1(X0,X3))
      | ~ v1_relat_1(k5_relat_1(X1,X2))
      | ~ r2_hidden(k4_tarski(sK5(X0,X3,sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),sK4(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2)))),k5_relat_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f861,f19])).

fof(f861,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(k5_relat_1(X0,k5_relat_1(X1,X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X0,X3))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),k5_relat_1(X0,X3))
      | ~ v1_relat_1(k5_relat_1(X1,X2))
      | ~ r2_hidden(k4_tarski(sK5(X0,X3,sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),sK4(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2)))),k5_relat_1(X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f858])).

fof(f858,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(k5_relat_1(X0,k5_relat_1(X1,X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X0,X3))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),k5_relat_1(X0,X3))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k5_relat_1(X1,X2))
      | ~ r2_hidden(k4_tarski(sK5(X0,X3,sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),sK4(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2)))),k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK5(X0,X3,sK3(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2))),X4),sK4(k5_relat_1(X0,X1),X2,k5_relat_1(X0,k5_relat_1(X1,X2)))),k5_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f619,f21])).

fof(f619,plain,(
    ! [X6,X4,X10,X8,X7,X5,X9] :
      ( ~ r2_hidden(k4_tarski(sK5(X4,X5,sK5(X6,X7,sK3(k5_relat_1(X6,X4),X8,k5_relat_1(X6,k5_relat_1(X4,X8))),X9),X10),sK4(k5_relat_1(X6,X4),X8,k5_relat_1(X6,k5_relat_1(X4,X8)))),X8)
      | k5_relat_1(X6,k5_relat_1(X4,X8)) = k5_relat_1(k5_relat_1(X6,X4),X8)
      | ~ v1_relat_1(k5_relat_1(X6,k5_relat_1(X4,X8)))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(k5_relat_1(X6,X4))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X6,X4),X8,k5_relat_1(X6,k5_relat_1(X4,X8))),X9),k5_relat_1(X6,X7))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(k5_relat_1(X4,X5))
      | ~ r2_hidden(k4_tarski(sK5(X6,X7,sK3(k5_relat_1(X6,X4),X8,k5_relat_1(X6,k5_relat_1(X4,X8))),X9),X10),k5_relat_1(X4,X5)) ) ),
    inference(duplicate_literal_removal,[],[f616])).

fof(f616,plain,(
    ! [X6,X4,X10,X8,X7,X5,X9] :
      ( ~ r2_hidden(k4_tarski(sK5(X4,X5,sK5(X6,X7,sK3(k5_relat_1(X6,X4),X8,k5_relat_1(X6,k5_relat_1(X4,X8))),X9),X10),sK4(k5_relat_1(X6,X4),X8,k5_relat_1(X6,k5_relat_1(X4,X8)))),X8)
      | k5_relat_1(X6,k5_relat_1(X4,X8)) = k5_relat_1(k5_relat_1(X6,X4),X8)
      | ~ v1_relat_1(k5_relat_1(X6,k5_relat_1(X4,X8)))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(k5_relat_1(X6,X4))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X6,X4),X8,k5_relat_1(X6,k5_relat_1(X4,X8))),X9),k5_relat_1(X6,X7))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(k5_relat_1(X4,X5))
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(sK5(X6,X7,sK3(k5_relat_1(X6,X4),X8,k5_relat_1(X6,k5_relat_1(X4,X8))),X9),X10),k5_relat_1(X4,X5)) ) ),
    inference(resolution,[],[f614,f22])).

fof(f614,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK5(X2,X4,sK3(k5_relat_1(X2,X0),X3,k5_relat_1(X2,k5_relat_1(X0,X3))),X5),X1),X0)
      | ~ r2_hidden(k4_tarski(X1,sK4(k5_relat_1(X2,X0),X3,k5_relat_1(X2,k5_relat_1(X0,X3)))),X3)
      | k5_relat_1(X2,k5_relat_1(X0,X3)) = k5_relat_1(k5_relat_1(X2,X0),X3)
      | ~ v1_relat_1(k5_relat_1(X2,k5_relat_1(X0,X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k5_relat_1(X2,X4))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X2,X0),X3,k5_relat_1(X2,k5_relat_1(X0,X3))),X5),k5_relat_1(X2,X4)) ) ),
    inference(duplicate_literal_removal,[],[f611])).

fof(f611,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X1,sK4(k5_relat_1(X2,X0),X3,k5_relat_1(X2,k5_relat_1(X0,X3)))),X3)
      | k5_relat_1(X2,k5_relat_1(X0,X3)) = k5_relat_1(k5_relat_1(X2,X0),X3)
      | ~ v1_relat_1(k5_relat_1(X2,k5_relat_1(X0,X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(sK5(X2,X4,sK3(k5_relat_1(X2,X0),X3,k5_relat_1(X2,k5_relat_1(X0,X3))),X5),X1),X0)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k5_relat_1(X2,X4))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X2,X0),X3,k5_relat_1(X2,k5_relat_1(X0,X3))),X5),k5_relat_1(X2,X4)) ) ),
    inference(resolution,[],[f598,f22])).

fof(f598,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X0,X1),X3,k5_relat_1(X0,k5_relat_1(X1,X3))),X4),X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,sK4(k5_relat_1(X0,X1),X3,k5_relat_1(X0,k5_relat_1(X1,X3)))),X3)
      | k5_relat_1(X0,k5_relat_1(X1,X3)) = k5_relat_1(k5_relat_1(X0,X1),X3)
      | ~ v1_relat_1(k5_relat_1(X0,k5_relat_1(X1,X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X2),X1) ) ),
    inference(duplicate_literal_removal,[],[f591])).

fof(f591,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,sK4(k5_relat_1(X0,X1),X3,k5_relat_1(X0,k5_relat_1(X1,X3)))),X3)
      | k5_relat_1(X0,k5_relat_1(X1,X3)) = k5_relat_1(k5_relat_1(X0,X1),X3)
      | ~ v1_relat_1(k5_relat_1(X0,k5_relat_1(X1,X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(sK3(k5_relat_1(X0,X1),X3,k5_relat_1(X0,k5_relat_1(X1,X3))),X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X2),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f590,f20])).

fof(f41,plain,
    ( k5_relat_1(k5_relat_1(sK0,sK1),sK2) != k5_relat_1(sK0,k5_relat_1(sK1,sK2))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl7_4
  <=> k5_relat_1(k5_relat_1(sK0,sK1),sK2) = k5_relat_1(sK0,k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f26,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl7_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f36,plain,
    ( v1_relat_1(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl7_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f31,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl7_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f42,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f10,f39])).

fof(f10,plain,(
    k5_relat_1(k5_relat_1(sK0,sK1),sK2) != k5_relat_1(sK0,k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) != k5_relat_1(X0,k5_relat_1(X1,X2))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f37,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f12,f34])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f32,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f11,f29])).

fof(f11,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f27,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f9,f24])).

fof(f9,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
