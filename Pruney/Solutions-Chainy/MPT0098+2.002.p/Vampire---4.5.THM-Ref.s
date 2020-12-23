%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:47 EST 2020

% Result     : Theorem 34.50s
% Output     : Refutation 34.50s
% Verified   : 
% Statistics : Number of formulae       :  177 (28314 expanded)
%              Number of leaves         :   11 (6766 expanded)
%              Depth                    :   46
%              Number of atoms          :  617 (183968 expanded)
%              Number of equality atoms :  102 (17327 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98906,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94397,f94488,f95545,f95699,f95833,f97561,f97686,f97807,f98643,f98725,f98780,f98893])).

fof(f98893,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f98892])).

fof(f98892,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f98871,f98761])).

fof(f98761,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f98760,f94487])).

fof(f94487,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f94485])).

fof(f94485,plain,
    ( spl4_4
  <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f98760,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f97888,f10451])).

fof(f10451,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f14,f10010])).

fof(f10010,plain,(
    ! [X10,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(superposition,[],[f9989,f6351])).

fof(f6351,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X5 ),
    inference(subsumption_resolution,[],[f6350,f6062])).

fof(f6062,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(sK3(X12,X13,k5_xboole_0(X12,X14)),X14)
      | r2_hidden(sK3(X12,X13,k5_xboole_0(X12,X14)),X13)
      | k5_xboole_0(X13,k5_xboole_0(X12,X14)) = X12 ) ),
    inference(subsumption_resolution,[],[f5952,f34])).

fof(f34,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X6)
      | k5_xboole_0(X5,k5_xboole_0(X6,X7)) = X4
      | ~ r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X4)
      | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X7)
      | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X5) ) ),
    inference(resolution,[],[f16,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k5_xboole_0(X1,X2) = X0
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ( ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) ) )
          | r2_hidden(sK3(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK3(X0,X1,X2),X1)
              | ~ r2_hidden(sK3(X0,X1,X2),X2) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | ~ r2_hidden(X3,X0) ) )
     => ( ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | r2_hidden(sK3(X0,X1,X2),X1) ) )
          | r2_hidden(sK3(X0,X1,X2),X0) )
        & ( ( ( r2_hidden(sK3(X0,X1,X2),X1)
              | ~ r2_hidden(sK3(X0,X1,X2),X2) )
            & ( r2_hidden(sK3(X0,X1,X2),X2)
              | ~ r2_hidden(sK3(X0,X1,X2),X1) ) )
          | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ( ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | ~ r2_hidden(X3,X0) ) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r2_hidden(X3,X0)
        <~> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_0)).

fof(f5952,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(sK3(X12,X13,k5_xboole_0(X12,X14)),X14)
      | r2_hidden(sK3(X12,X13,k5_xboole_0(X12,X14)),X12)
      | r2_hidden(sK3(X12,X13,k5_xboole_0(X12,X14)),X13)
      | k5_xboole_0(X13,k5_xboole_0(X12,X14)) = X12 ) ),
    inference(factoring,[],[f38])).

fof(f38,plain,(
    ! [X12,X10,X11,X9] :
      ( r2_hidden(sK3(X9,X10,k5_xboole_0(X11,X12)),X12)
      | r2_hidden(sK3(X9,X10,k5_xboole_0(X11,X12)),X11)
      | r2_hidden(sK3(X9,X10,k5_xboole_0(X11,X12)),X10)
      | r2_hidden(sK3(X9,X10,k5_xboole_0(X11,X12)),X9)
      | k5_xboole_0(X10,k5_xboole_0(X11,X12)) = X9 ) ),
    inference(resolution,[],[f17,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k5_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6350,plain,(
    ! [X4,X5] :
      ( k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X5
      | ~ r2_hidden(sK3(X5,X4,k5_xboole_0(X5,X4)),X4) ) ),
    inference(subsumption_resolution,[],[f6336,f79])).

fof(f79,plain,(
    ! [X14,X12,X13,X11] :
      ( ~ r2_hidden(sK3(X14,X11,k5_xboole_0(X12,X13)),X13)
      | ~ r2_hidden(sK3(X14,X11,k5_xboole_0(X12,X13)),X11)
      | r2_hidden(sK3(X14,X11,k5_xboole_0(X12,X13)),X14)
      | r2_hidden(sK3(X14,X11,k5_xboole_0(X12,X13)),X12)
      | k5_xboole_0(X11,k5_xboole_0(X12,X13)) = X14 ) ),
    inference(resolution,[],[f18,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k5_xboole_0(X1,X2) = X0
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6336,plain,(
    ! [X4,X5] :
      ( k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X5
      | ~ r2_hidden(sK3(X5,X4,k5_xboole_0(X5,X4)),X5)
      | ~ r2_hidden(sK3(X5,X4,k5_xboole_0(X5,X4)),X4) ) ),
    inference(resolution,[],[f6324,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6324,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK3(X11,X10,k5_xboole_0(X11,X10)),k5_xboole_0(X11,X10))
      | k5_xboole_0(X10,k5_xboole_0(X11,X10)) = X11 ) ),
    inference(subsumption_resolution,[],[f6318,f6059])).

fof(f6059,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X5)
      | r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X3)
      | k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X3 ) ),
    inference(subsumption_resolution,[],[f5949,f79])).

fof(f5949,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X4)
      | r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X5)
      | r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X3)
      | k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X3 ) ),
    inference(factoring,[],[f38])).

fof(f6318,plain,(
    ! [X10,X11] :
      ( k5_xboole_0(X10,k5_xboole_0(X11,X10)) = X11
      | r2_hidden(sK3(X11,X10,k5_xboole_0(X11,X10)),k5_xboole_0(X11,X10))
      | ~ r2_hidden(sK3(X11,X10,k5_xboole_0(X11,X10)),X11) ) ),
    inference(duplicate_literal_removal,[],[f6304])).

fof(f6304,plain,(
    ! [X10,X11] :
      ( k5_xboole_0(X10,k5_xboole_0(X11,X10)) = X11
      | r2_hidden(sK3(X11,X10,k5_xboole_0(X11,X10)),k5_xboole_0(X11,X10))
      | k5_xboole_0(X10,k5_xboole_0(X11,X10)) = X11
      | ~ r2_hidden(sK3(X11,X10,k5_xboole_0(X11,X10)),X11) ) ),
    inference(resolution,[],[f6286,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k5_xboole_0(X1,X2) = X0
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6286,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X1)
      | k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ) ),
    inference(subsumption_resolution,[],[f6283,f38])).

fof(f6283,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2
      | ~ r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X2)
      | r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X1) ) ),
    inference(duplicate_literal_removal,[],[f6257])).

fof(f6257,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2
      | k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2
      | ~ r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X2)
      | r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X1)
      | r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X1) ) ),
    inference(resolution,[],[f6180,f34])).

fof(f6180,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,k5_xboole_0(X0,X1)),X0)
      | k5_xboole_0(X1,k5_xboole_0(X0,X1)) = X0 ) ),
    inference(factoring,[],[f6059])).

fof(f9989,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k5_xboole_0(X6,X7)) = X7 ),
    inference(subsumption_resolution,[],[f9988,f6061])).

fof(f6061,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(sK3(X9,X10,k5_xboole_0(X10,X11)),X11)
      | r2_hidden(sK3(X9,X10,k5_xboole_0(X10,X11)),X9)
      | k5_xboole_0(X10,k5_xboole_0(X10,X11)) = X9 ) ),
    inference(subsumption_resolution,[],[f5951,f80])).

fof(f80,plain,(
    ! [X17,X15,X18,X16] :
      ( ~ r2_hidden(sK3(X18,X15,k5_xboole_0(X16,X17)),X16)
      | ~ r2_hidden(sK3(X18,X15,k5_xboole_0(X16,X17)),X15)
      | r2_hidden(sK3(X18,X15,k5_xboole_0(X16,X17)),X18)
      | r2_hidden(sK3(X18,X15,k5_xboole_0(X16,X17)),X17)
      | k5_xboole_0(X15,k5_xboole_0(X16,X17)) = X18 ) ),
    inference(resolution,[],[f18,f21])).

fof(f5951,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(sK3(X9,X10,k5_xboole_0(X10,X11)),X11)
      | r2_hidden(sK3(X9,X10,k5_xboole_0(X10,X11)),X10)
      | r2_hidden(sK3(X9,X10,k5_xboole_0(X10,X11)),X9)
      | k5_xboole_0(X10,k5_xboole_0(X10,X11)) = X9 ) ),
    inference(factoring,[],[f38])).

fof(f9988,plain,(
    ! [X6,X7] :
      ( k5_xboole_0(X6,k5_xboole_0(X6,X7)) = X7
      | ~ r2_hidden(sK3(X7,X6,k5_xboole_0(X6,X7)),X7) ) ),
    inference(subsumption_resolution,[],[f9972,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK3(X0,X1,k5_xboole_0(X2,X3)),X3)
      | k5_xboole_0(X1,k5_xboole_0(X2,X3)) = X0
      | ~ r2_hidden(sK3(X0,X1,k5_xboole_0(X2,X3)),X0)
      | r2_hidden(sK3(X0,X1,k5_xboole_0(X2,X3)),X2)
      | r2_hidden(sK3(X0,X1,k5_xboole_0(X2,X3)),X1) ) ),
    inference(resolution,[],[f16,f22])).

fof(f9972,plain,(
    ! [X6,X7] :
      ( k5_xboole_0(X6,k5_xboole_0(X6,X7)) = X7
      | ~ r2_hidden(sK3(X7,X6,k5_xboole_0(X6,X7)),X6)
      | ~ r2_hidden(sK3(X7,X6,k5_xboole_0(X6,X7)),X7) ) ),
    inference(resolution,[],[f9741,f20])).

fof(f9741,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK3(X9,X8,k5_xboole_0(X8,X9)),k5_xboole_0(X8,X9))
      | k5_xboole_0(X8,k5_xboole_0(X8,X9)) = X9 ) ),
    inference(subsumption_resolution,[],[f9735,f7763])).

fof(f7763,plain,(
    ! [X19,X17,X20,X18] :
      ( r2_hidden(sK3(X19,X18,X20),k5_xboole_0(X18,X17))
      | r2_hidden(sK3(X19,X18,X20),X20)
      | r2_hidden(sK3(X19,X18,X20),X19)
      | r2_hidden(sK3(X19,X18,X20),X17)
      | k5_xboole_0(X18,X20) = X19 ) ),
    inference(superposition,[],[f42,f6351])).

fof(f42,plain,(
    ! [X12,X10,X11,X9] :
      ( r2_hidden(sK3(X9,k5_xboole_0(X10,X11),X12),X12)
      | r2_hidden(sK3(X9,k5_xboole_0(X10,X11),X12),X11)
      | r2_hidden(sK3(X9,k5_xboole_0(X10,X11),X12),X10)
      | r2_hidden(sK3(X9,k5_xboole_0(X10,X11),X12),X9)
      | k5_xboole_0(k5_xboole_0(X10,X11),X12) = X9 ) ),
    inference(resolution,[],[f17,f19])).

fof(f9735,plain,(
    ! [X8,X9] :
      ( k5_xboole_0(X8,k5_xboole_0(X8,X9)) = X9
      | r2_hidden(sK3(X9,X8,k5_xboole_0(X8,X9)),k5_xboole_0(X8,X9))
      | ~ r2_hidden(sK3(X9,X8,k5_xboole_0(X8,X9)),X9) ) ),
    inference(duplicate_literal_removal,[],[f9717])).

fof(f9717,plain,(
    ! [X8,X9] :
      ( k5_xboole_0(X8,k5_xboole_0(X8,X9)) = X9
      | r2_hidden(sK3(X9,X8,k5_xboole_0(X8,X9)),k5_xboole_0(X8,X9))
      | k5_xboole_0(X8,k5_xboole_0(X8,X9)) = X9
      | ~ r2_hidden(sK3(X9,X8,k5_xboole_0(X8,X9)),X9) ) ),
    inference(resolution,[],[f9328,f15])).

fof(f9328,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,k5_xboole_0(X1,X0)),X1)
      | k5_xboole_0(X1,k5_xboole_0(X1,X0)) = X0 ) ),
    inference(factoring,[],[f6060])).

fof(f6060,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK3(X6,X7,k5_xboole_0(X8,X6)),X8)
      | r2_hidden(sK3(X6,X7,k5_xboole_0(X8,X6)),X7)
      | k5_xboole_0(X7,k5_xboole_0(X8,X6)) = X6 ) ),
    inference(subsumption_resolution,[],[f5950,f33])).

fof(f5950,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK3(X6,X7,k5_xboole_0(X8,X6)),X6)
      | r2_hidden(sK3(X6,X7,k5_xboole_0(X8,X6)),X8)
      | r2_hidden(sK3(X6,X7,k5_xboole_0(X8,X6)),X7)
      | k5_xboole_0(X7,k5_xboole_0(X8,X6)) = X6 ) ),
    inference(factoring,[],[f38])).

fof(f14,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) != k5_xboole_0(X0,k5_xboole_0(X1,X2))
   => k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) != k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f97888,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ spl4_3 ),
    inference(resolution,[],[f94482,f18])).

fof(f94482,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f94481])).

fof(f94481,plain,
    ( spl4_3
  <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f98871,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f98828,f97614,f20])).

fof(f97614,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | ~ spl4_4
    | spl4_5 ),
    inference(forward_demodulation,[],[f97595,f10010])).

fof(f97595,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,sK1))
    | ~ spl4_4
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f95540,f94487,f21])).

fof(f95540,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f95538])).

fof(f95538,plain,
    ( spl4_5
  <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f98828,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)
    | ~ spl4_3
    | spl4_5 ),
    inference(forward_demodulation,[],[f98827,f6351])).

fof(f98827,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl4_3
    | spl4_5 ),
    inference(forward_demodulation,[],[f98812,f10010])).

fof(f98812,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,sK1),sK1))
    | ~ spl4_3
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f95540,f94482,f21])).

fof(f98780,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f98779])).

fof(f98779,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f98768,f98762])).

fof(f98762,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f94445,f97893])).

fof(f97893,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f97892,f6351])).

fof(f97892,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f97886,f10010])).

fof(f97886,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,sK1),sK1))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f95539,f94482,f20])).

fof(f95539,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f95538])).

fof(f94445,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f94422,f10451])).

fof(f94422,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)
    | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f94392,f8423])).

fof(f8423,plain,(
    ! [X70,X72,X71,X73] :
      ( r2_hidden(sK3(k5_xboole_0(X70,X71),X72,X73),k5_xboole_0(X72,X73))
      | r2_hidden(sK3(k5_xboole_0(X70,X71),X72,X73),X71)
      | r2_hidden(sK3(k5_xboole_0(X70,X71),X72,X73),X70)
      | k5_xboole_0(X70,X71) = k5_xboole_0(X72,X73) ) ),
    inference(resolution,[],[f7233,f19])).

fof(f7233,plain,(
    ! [X35,X33,X34] :
      ( r2_hidden(sK3(X35,X33,X34),k5_xboole_0(X33,X34))
      | r2_hidden(sK3(X35,X33,X34),X35)
      | k5_xboole_0(X33,X34) = X35 ) ),
    inference(superposition,[],[f6357,f6389])).

fof(f6389,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    inference(superposition,[],[f6351,f6351])).

fof(f6357,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X5)
      | r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X3)
      | X3 = X5 ) ),
    inference(backward_demodulation,[],[f6059,f6351])).

fof(f94392,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f94390])).

fof(f94390,plain,
    ( spl4_1
  <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f98768,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f95539,f94487,f20])).

fof(f98725,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f98724])).

fof(f98724,plain,
    ( $false
    | spl4_2
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f98708,f97703])).

fof(f97703,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | spl4_2
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f94396,f95544,f21])).

fof(f95544,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f95542])).

fof(f95542,plain,
    ( spl4_6
  <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f94396,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f94394])).

fof(f94394,plain,
    ( spl4_2
  <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f98708,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | spl4_2
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f95539,f98648,f20])).

fof(f98648,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f10451,f95539,f94396,f95544,f37])).

fof(f37,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(sK3(X5,X6,k5_xboole_0(X7,X8)),X8)
      | r2_hidden(sK3(X5,X6,k5_xboole_0(X7,X8)),X5)
      | k5_xboole_0(X6,k5_xboole_0(X7,X8)) = X5
      | ~ r2_hidden(sK3(X5,X6,k5_xboole_0(X7,X8)),X7)
      | r2_hidden(sK3(X5,X6,k5_xboole_0(X7,X8)),X6) ) ),
    inference(resolution,[],[f17,f20])).

fof(f98643,plain,
    ( spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f98642])).

fof(f98642,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f98605,f98548])).

fof(f98548,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f95539,f97894,f21])).

fof(f97894,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f97884,f6351])).

fof(f97884,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))))
    | spl4_2
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f97400,f94482,f20])).

fof(f97400,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f76871,f94396,f19])).

fof(f76871,plain,(
    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f76764,f10010])).

fof(f76764,plain,(
    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f10451,f75402])).

fof(f75402,plain,(
    ! [X14,X15,X13] :
      ( r2_hidden(sK3(X15,X14,X13),k5_xboole_0(k5_xboole_0(X14,X13),X15))
      | k5_xboole_0(X14,X13) = X15 ) ),
    inference(superposition,[],[f75284,f6351])).

fof(f75284,plain,(
    ! [X161,X162,X160] :
      ( r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),k5_xboole_0(X162,X160))
      | X160 = X162 ) ),
    inference(subsumption_resolution,[],[f75283,f75278])).

fof(f75278,plain,(
    ! [X64,X62,X63] :
      ( r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),k5_xboole_0(X64,X62))
      | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X63)
      | X62 = X64 ) ),
    inference(duplicate_literal_removal,[],[f75277])).

fof(f75277,plain,(
    ! [X64,X62,X63] :
      ( X62 = X64
      | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),k5_xboole_0(X64,X62))
      | X62 = X64
      | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X63) ) ),
    inference(forward_demodulation,[],[f75276,f9989])).

fof(f75276,plain,(
    ! [X64,X62,X63] :
      ( k5_xboole_0(X63,k5_xboole_0(X63,X64)) = X62
      | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),k5_xboole_0(X64,X62))
      | X62 = X64
      | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X63) ) ),
    inference(forward_demodulation,[],[f75275,f10010])).

fof(f75275,plain,(
    ! [X64,X62,X63] :
      ( r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),k5_xboole_0(X64,X62))
      | X62 = X64
      | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X63)
      | k5_xboole_0(k5_xboole_0(X63,X64),X63) = X62 ) ),
    inference(subsumption_resolution,[],[f75076,f66071])).

fof(f66071,plain,(
    ! [X14,X15,X13] :
      ( r2_hidden(sK3(X15,k5_xboole_0(X14,X13),X14),k5_xboole_0(X13,X15))
      | r2_hidden(sK3(X15,k5_xboole_0(X14,X13),X14),X15)
      | X13 = X15 ) ),
    inference(superposition,[],[f65825,f6351])).

fof(f65825,plain,(
    ! [X14,X15,X13] :
      ( r2_hidden(sK3(X13,X15,k5_xboole_0(X14,X15)),k5_xboole_0(X14,X13))
      | r2_hidden(sK3(X13,X15,k5_xboole_0(X14,X15)),X13)
      | X13 = X14 ) ),
    inference(superposition,[],[f61732,f6351])).

fof(f61732,plain,(
    ! [X88,X87,X86] :
      ( r2_hidden(sK3(X86,X87,k5_xboole_0(k5_xboole_0(X86,X88),X87)),X88)
      | r2_hidden(sK3(X86,X87,k5_xboole_0(k5_xboole_0(X86,X88),X87)),X86)
      | k5_xboole_0(X86,X88) = X86 ) ),
    inference(duplicate_literal_removal,[],[f61698])).

fof(f61698,plain,(
    ! [X88,X87,X86] :
      ( r2_hidden(sK3(X86,X87,k5_xboole_0(k5_xboole_0(X86,X88),X87)),X88)
      | k5_xboole_0(X86,X88) = X86
      | r2_hidden(sK3(X86,X87,k5_xboole_0(k5_xboole_0(X86,X88),X87)),X86)
      | r2_hidden(sK3(X86,X87,k5_xboole_0(k5_xboole_0(X86,X88),X87)),X88) ) ),
    inference(resolution,[],[f61503,f19])).

fof(f61503,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,k5_xboole_0(k5_xboole_0(X0,X2),X1)),k5_xboole_0(X0,X2))
      | r2_hidden(sK3(X0,X1,k5_xboole_0(k5_xboole_0(X0,X2),X1)),X2)
      | k5_xboole_0(X0,X2) = X0 ) ),
    inference(factoring,[],[f58939])).

fof(f58939,plain,(
    ! [X19,X17,X20,X18] :
      ( r2_hidden(sK3(X19,X17,k5_xboole_0(X18,X17)),k5_xboole_0(X19,X20))
      | r2_hidden(sK3(X19,X17,k5_xboole_0(X18,X17)),X18)
      | r2_hidden(sK3(X19,X17,k5_xboole_0(X18,X17)),X20)
      | X18 = X19 ) ),
    inference(superposition,[],[f58512,f6351])).

fof(f58512,plain,(
    ! [X19,X17,X20,X18] :
      ( r2_hidden(sK3(X18,X19,X20),k5_xboole_0(X19,X20))
      | r2_hidden(sK3(X18,X19,X20),k5_xboole_0(X18,X17))
      | r2_hidden(sK3(X18,X19,X20),X17)
      | k5_xboole_0(X19,X20) = X18 ) ),
    inference(superposition,[],[f8423,f6351])).

fof(f75076,plain,(
    ! [X64,X62,X63] :
      ( r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),k5_xboole_0(X64,X62))
      | X62 = X64
      | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X63)
      | k5_xboole_0(k5_xboole_0(X63,X64),X63) = X62
      | ~ r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X62) ) ),
    inference(resolution,[],[f69741,f15])).

fof(f69741,plain,(
    ! [X14,X15,X13] :
      ( r2_hidden(sK3(X15,k5_xboole_0(X14,X13),X14),k5_xboole_0(X14,X13))
      | r2_hidden(sK3(X15,k5_xboole_0(X14,X13),X14),k5_xboole_0(X13,X15))
      | X13 = X15 ) ),
    inference(superposition,[],[f69224,f6351])).

fof(f69224,plain,(
    ! [X14,X15,X13] :
      ( r2_hidden(sK3(X13,X15,k5_xboole_0(X14,X15)),k5_xboole_0(X14,X13))
      | r2_hidden(sK3(X13,X15,k5_xboole_0(X14,X15)),X15)
      | X13 = X14 ) ),
    inference(superposition,[],[f61748,f6351])).

fof(f61748,plain,(
    ! [X23,X21,X22] :
      ( r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X23)
      | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22)
      | k5_xboole_0(X21,X23) = X21 ) ),
    inference(duplicate_literal_removal,[],[f61747])).

fof(f61747,plain,(
    ! [X23,X21,X22] :
      ( k5_xboole_0(X21,X23) = X21
      | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X23)
      | k5_xboole_0(X21,X23) = X21
      | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22) ) ),
    inference(forward_demodulation,[],[f61746,f6351])).

fof(f61746,plain,(
    ! [X23,X21,X22] :
      ( r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X23)
      | k5_xboole_0(X21,X23) = X21
      | k5_xboole_0(X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)) = X21
      | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22) ) ),
    inference(subsumption_resolution,[],[f61736,f5899])).

fof(f5899,plain,(
    ! [X80,X78,X81,X79,X82] :
      ( r2_hidden(sK3(X78,X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)),X82)
      | r2_hidden(sK3(X78,X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)),X81)
      | r2_hidden(sK3(X78,X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)),X80)
      | r2_hidden(sK3(X78,X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)),X79)
      | r2_hidden(sK3(X78,X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)),X78)
      | k5_xboole_0(X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)) = X78 ) ),
    inference(resolution,[],[f38,f19])).

fof(f61736,plain,(
    ! [X23,X21,X22] :
      ( r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X23)
      | k5_xboole_0(X21,X23) = X21
      | k5_xboole_0(X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)) = X21
      | ~ r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X21)
      | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22) ) ),
    inference(duplicate_literal_removal,[],[f61671])).

fof(f61671,plain,(
    ! [X23,X21,X22] :
      ( r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X23)
      | k5_xboole_0(X21,X23) = X21
      | k5_xboole_0(X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)) = X21
      | ~ r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X21)
      | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22)
      | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22) ) ),
    inference(resolution,[],[f61503,f34])).

fof(f75283,plain,(
    ! [X161,X162,X160] :
      ( r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),k5_xboole_0(X162,X160))
      | X160 = X162
      | ~ r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),X161) ) ),
    inference(subsumption_resolution,[],[f75118,f59253])).

fof(f59253,plain,(
    ! [X57,X54,X56,X55] :
      ( r2_hidden(sK3(X56,k5_xboole_0(X54,X55),X54),X55)
      | r2_hidden(sK3(X56,k5_xboole_0(X54,X55),X54),k5_xboole_0(X57,X56))
      | r2_hidden(sK3(X56,k5_xboole_0(X54,X55),X54),X57)
      | X55 = X56 ) ),
    inference(superposition,[],[f58513,f6389])).

fof(f58513,plain,(
    ! [X24,X23,X21,X22] :
      ( r2_hidden(sK3(X22,X23,X24),k5_xboole_0(X23,X24))
      | r2_hidden(sK3(X22,X23,X24),k5_xboole_0(X21,X22))
      | r2_hidden(sK3(X22,X23,X24),X21)
      | k5_xboole_0(X23,X24) = X22 ) ),
    inference(superposition,[],[f8423,f9989])).

fof(f75118,plain,(
    ! [X161,X162,X160] :
      ( r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),k5_xboole_0(X162,X160))
      | X160 = X162
      | ~ r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),X161)
      | ~ r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),X162) ) ),
    inference(resolution,[],[f69741,f20])).

fof(f98605,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f94396,f97893,f22])).

fof(f97807,plain,
    ( spl4_2
    | spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f97806])).

fof(f97806,plain,
    ( $false
    | spl4_2
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f97783,f97703])).

fof(f97783,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | spl4_2
    | spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f95540,f97692,f19])).

fof(f97692,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | spl4_2
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f97691,f10451])).

fof(f97691,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))
    | spl4_2
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f97690,f95540])).

fof(f97690,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1)
    | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f95737,f94396])).

fof(f95737,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1)
    | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f95544,f80])).

fof(f97686,plain,
    ( spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f97685])).

fof(f97685,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f97647,f97614])).

fof(f97647,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f94396,f97627,f22])).

fof(f97627,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)
    | spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(forward_demodulation,[],[f97571,f6351])).

fof(f97571,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f10451,f95540,f94396,f94487,f10977])).

fof(f10977,plain,(
    ! [X24,X23,X21,X22] :
      ( ~ r2_hidden(sK3(X23,X24,X22),k5_xboole_0(X21,X22))
      | ~ r2_hidden(sK3(X23,X24,X22),X24)
      | r2_hidden(sK3(X23,X24,X22),X23)
      | r2_hidden(sK3(X23,X24,X22),X21)
      | k5_xboole_0(X24,X22) = X23 ) ),
    inference(superposition,[],[f79,f9989])).

fof(f97561,plain,
    ( spl4_4
    | spl4_6
    | spl4_2
    | spl4_5 ),
    inference(avatar_split_clause,[],[f97459,f95538,f94394,f95542,f94485])).

fof(f97459,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | spl4_2
    | spl4_5 ),
    inference(subsumption_resolution,[],[f97458,f10451])).

fof(f97458,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))
    | spl4_2
    | spl4_5 ),
    inference(subsumption_resolution,[],[f97401,f95540])).

fof(f97401,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(resolution,[],[f94396,f38])).

fof(f95833,plain,
    ( spl4_1
    | spl4_3
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f95832])).

fof(f95832,plain,
    ( $false
    | spl4_1
    | spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f95831,f95736])).

fof(f95736,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | spl4_1
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f94419,f95544,f20])).

fof(f94419,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f76871,f94392,f19])).

fof(f95831,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | spl4_1
    | spl4_3
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f95767,f10010])).

fof(f95767,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,sK1))
    | spl4_1
    | spl4_3
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f10451,f94483,f94419,f95720,f6425])).

fof(f6425,plain,(
    ! [X92,X90,X93,X91] :
      ( ~ r2_hidden(sK3(X92,X91,X93),X92)
      | k5_xboole_0(X91,X93) = X92
      | ~ r2_hidden(sK3(X92,X91,X93),X90)
      | r2_hidden(sK3(X92,X91,X93),k5_xboole_0(X91,X90))
      | r2_hidden(sK3(X92,X91,X93),X93) ) ),
    inference(superposition,[],[f32,f6351])).

fof(f32,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(sK3(X4,k5_xboole_0(X5,X6),X7),X5)
      | k5_xboole_0(k5_xboole_0(X5,X6),X7) = X4
      | ~ r2_hidden(sK3(X4,k5_xboole_0(X5,X6),X7),X4)
      | r2_hidden(sK3(X4,k5_xboole_0(X5,X6),X7),X6)
      | r2_hidden(sK3(X4,k5_xboole_0(X5,X6),X7),X7) ) ),
    inference(resolution,[],[f15,f21])).

fof(f95720,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1)
    | spl4_3
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f94483,f95544,f21])).

fof(f94483,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f94481])).

fof(f95699,plain,
    ( spl4_1
    | spl4_3
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f95698])).

fof(f95698,plain,
    ( $false
    | spl4_1
    | spl4_3
    | spl4_5 ),
    inference(subsumption_resolution,[],[f95603,f95579])).

fof(f95579,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | spl4_1
    | spl4_3
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f95172,f95540,f19])).

fof(f95172,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | spl4_1
    | spl4_3 ),
    inference(forward_demodulation,[],[f95157,f6351])).

fof(f95157,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))))
    | spl4_1
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f94392,f94483,f19])).

fof(f95603,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))
    | spl4_1
    | spl4_3
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f10451,f95540,f95584,f95172,f95584,f5945])).

fof(f5945,plain,(
    ! [X70,X68,X66,X69,X67] :
      ( r2_hidden(sK3(k5_xboole_0(X66,X67),X68,k5_xboole_0(X69,X70)),X70)
      | r2_hidden(sK3(k5_xboole_0(X66,X67),X68,k5_xboole_0(X69,X70)),X69)
      | r2_hidden(sK3(k5_xboole_0(X66,X67),X68,k5_xboole_0(X69,X70)),X68)
      | r2_hidden(sK3(k5_xboole_0(X66,X67),X68,k5_xboole_0(X69,X70)),X67)
      | r2_hidden(sK3(k5_xboole_0(X66,X67),X68,k5_xboole_0(X69,X70)),X66)
      | k5_xboole_0(X68,k5_xboole_0(X69,X70)) = k5_xboole_0(X66,X67) ) ),
    inference(resolution,[],[f38,f19])).

fof(f95584,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)
    | spl4_3
    | spl4_5 ),
    inference(forward_demodulation,[],[f95577,f6351])).

fof(f95577,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | spl4_3
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f94483,f95540,f19])).

fof(f95545,plain,
    ( ~ spl4_5
    | spl4_6
    | spl4_3 ),
    inference(avatar_split_clause,[],[f95169,f94481,f95542,f95538])).

fof(f95169,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1)
    | spl4_3 ),
    inference(resolution,[],[f94483,f22])).

fof(f94488,plain,
    ( ~ spl4_3
    | spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f94428,f94390,f94485,f94481])).

fof(f94428,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f94392,f22])).

fof(f94397,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f83061,f94394,f94390])).

fof(f83061,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f76871,f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (6156)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.19/0.41  % (6154)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.43  % (6149)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.44  % (6158)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.44  % (6150)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.44  % (6155)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.44  % (6152)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.45  % (6160)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.45  % (6151)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.47  % (6157)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.48  % (6153)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.48  % (6148)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 4.75/1.01  % (6149)Time limit reached!
% 4.75/1.01  % (6149)------------------------------
% 4.75/1.01  % (6149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.75/1.01  % (6149)Termination reason: Time limit
% 4.75/1.01  % (6149)Termination phase: Saturation
% 4.75/1.01  
% 4.75/1.01  % (6149)Memory used [KB]: 18293
% 4.75/1.01  % (6149)Time elapsed: 0.600 s
% 4.75/1.01  % (6149)------------------------------
% 4.75/1.01  % (6149)------------------------------
% 8.18/1.44  % (6148)Time limit reached!
% 8.18/1.44  % (6148)------------------------------
% 8.18/1.44  % (6148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.18/1.44  % (6148)Termination reason: Time limit
% 8.18/1.44  % (6148)Termination phase: Saturation
% 8.18/1.44  
% 8.18/1.44  % (6148)Memory used [KB]: 36204
% 8.18/1.44  % (6148)Time elapsed: 1.0000 s
% 8.18/1.44  % (6148)------------------------------
% 8.18/1.44  % (6148)------------------------------
% 34.50/4.75  % (6150)Refutation found. Thanks to Tanya!
% 34.50/4.75  % SZS status Theorem for theBenchmark
% 34.50/4.75  % SZS output start Proof for theBenchmark
% 34.50/4.75  fof(f98906,plain,(
% 34.50/4.75    $false),
% 34.50/4.75    inference(avatar_sat_refutation,[],[f94397,f94488,f95545,f95699,f95833,f97561,f97686,f97807,f98643,f98725,f98780,f98893])).
% 34.50/4.75  fof(f98893,plain,(
% 34.50/4.75    ~spl4_3 | ~spl4_4 | spl4_5),
% 34.50/4.75    inference(avatar_contradiction_clause,[],[f98892])).
% 34.50/4.75  fof(f98892,plain,(
% 34.50/4.75    $false | (~spl4_3 | ~spl4_4 | spl4_5)),
% 34.50/4.75    inference(subsumption_resolution,[],[f98871,f98761])).
% 34.50/4.75  fof(f98761,plain,(
% 34.50/4.75    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | (~spl4_3 | ~spl4_4)),
% 34.50/4.75    inference(subsumption_resolution,[],[f98760,f94487])).
% 34.50/4.75  fof(f94487,plain,(
% 34.50/4.75    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | ~spl4_4),
% 34.50/4.75    inference(avatar_component_clause,[],[f94485])).
% 34.50/4.75  fof(f94485,plain,(
% 34.50/4.75    spl4_4 <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2)),
% 34.50/4.75    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 34.50/4.75  fof(f98760,plain,(
% 34.50/4.75    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | ~spl4_3),
% 34.50/4.75    inference(subsumption_resolution,[],[f97888,f10451])).
% 34.50/4.75  fof(f10451,plain,(
% 34.50/4.75    k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))),
% 34.50/4.75    inference(superposition,[],[f14,f10010])).
% 34.50/4.75  fof(f10010,plain,(
% 34.50/4.75    ( ! [X10,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9)) )),
% 34.50/4.75    inference(superposition,[],[f9989,f6351])).
% 34.50/4.75  fof(f6351,plain,(
% 34.50/4.75    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X5) )),
% 34.50/4.75    inference(subsumption_resolution,[],[f6350,f6062])).
% 34.50/4.75  fof(f6062,plain,(
% 34.50/4.75    ( ! [X14,X12,X13] : (r2_hidden(sK3(X12,X13,k5_xboole_0(X12,X14)),X14) | r2_hidden(sK3(X12,X13,k5_xboole_0(X12,X14)),X13) | k5_xboole_0(X13,k5_xboole_0(X12,X14)) = X12) )),
% 34.50/4.75    inference(subsumption_resolution,[],[f5952,f34])).
% 34.50/4.75  fof(f34,plain,(
% 34.50/4.75    ( ! [X6,X4,X7,X5] : (~r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X6) | k5_xboole_0(X5,k5_xboole_0(X6,X7)) = X4 | ~r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X4) | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X7) | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X5)) )),
% 34.50/4.75    inference(resolution,[],[f16,f21])).
% 34.50/4.75  fof(f21,plain,(
% 34.50/4.75    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 34.50/4.75    inference(cnf_transformation,[],[f13])).
% 34.50/4.75  fof(f13,plain,(
% 34.50/4.75    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 34.50/4.75    inference(nnf_transformation,[],[f7])).
% 34.50/4.75  fof(f7,plain,(
% 34.50/4.75    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 34.50/4.75    inference(ennf_transformation,[],[f1])).
% 34.50/4.75  fof(f1,axiom,(
% 34.50/4.75    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 34.50/4.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 34.50/4.75  fof(f16,plain,(
% 34.50/4.75    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | k5_xboole_0(X1,X2) = X0 | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 34.50/4.75    inference(cnf_transformation,[],[f12])).
% 34.50/4.75  fof(f12,plain,(
% 34.50/4.75    ! [X0,X1,X2] : (k5_xboole_0(X1,X2) = X0 | ((((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1))) | r2_hidden(sK3(X0,X1,X2),X0)) & (((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1))) | ~r2_hidden(sK3(X0,X1,X2),X0))))),
% 34.50/4.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).
% 34.50/4.75  fof(f11,plain,(
% 34.50/4.75    ! [X2,X1,X0] : (? [X3] : ((((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | r2_hidden(X3,X0)) & (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~r2_hidden(X3,X0))) => ((((~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) & (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1))) | r2_hidden(sK3(X0,X1,X2),X0)) & (((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1))) | ~r2_hidden(sK3(X0,X1,X2),X0))))),
% 34.50/4.75    introduced(choice_axiom,[])).
% 34.50/4.75  fof(f10,plain,(
% 34.50/4.75    ! [X0,X1,X2] : (k5_xboole_0(X1,X2) = X0 | ? [X3] : ((((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) | r2_hidden(X3,X0)) & (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~r2_hidden(X3,X0))))),
% 34.50/4.75    inference(nnf_transformation,[],[f6])).
% 34.50/4.75  fof(f6,plain,(
% 34.50/4.75    ! [X0,X1,X2] : (k5_xboole_0(X1,X2) = X0 | ? [X3] : (~r2_hidden(X3,X0) <~> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))))),
% 34.50/4.75    inference(ennf_transformation,[],[f2])).
% 34.50/4.75  fof(f2,axiom,(
% 34.50/4.75    ! [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,X0) <=> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k5_xboole_0(X1,X2) = X0)),
% 34.50/4.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_0)).
% 34.50/4.75  fof(f5952,plain,(
% 34.50/4.75    ( ! [X14,X12,X13] : (r2_hidden(sK3(X12,X13,k5_xboole_0(X12,X14)),X14) | r2_hidden(sK3(X12,X13,k5_xboole_0(X12,X14)),X12) | r2_hidden(sK3(X12,X13,k5_xboole_0(X12,X14)),X13) | k5_xboole_0(X13,k5_xboole_0(X12,X14)) = X12) )),
% 34.50/4.75    inference(factoring,[],[f38])).
% 34.50/4.75  fof(f38,plain,(
% 34.50/4.75    ( ! [X12,X10,X11,X9] : (r2_hidden(sK3(X9,X10,k5_xboole_0(X11,X12)),X12) | r2_hidden(sK3(X9,X10,k5_xboole_0(X11,X12)),X11) | r2_hidden(sK3(X9,X10,k5_xboole_0(X11,X12)),X10) | r2_hidden(sK3(X9,X10,k5_xboole_0(X11,X12)),X9) | k5_xboole_0(X10,k5_xboole_0(X11,X12)) = X9) )),
% 34.50/4.75    inference(resolution,[],[f17,f19])).
% 34.50/4.75  fof(f19,plain,(
% 34.50/4.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 34.50/4.75    inference(cnf_transformation,[],[f13])).
% 34.50/4.75  fof(f17,plain,(
% 34.50/4.75    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | k5_xboole_0(X1,X2) = X0) )),
% 34.50/4.75    inference(cnf_transformation,[],[f12])).
% 34.50/4.75  fof(f6350,plain,(
% 34.50/4.75    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X5 | ~r2_hidden(sK3(X5,X4,k5_xboole_0(X5,X4)),X4)) )),
% 34.50/4.75    inference(subsumption_resolution,[],[f6336,f79])).
% 34.50/4.75  fof(f79,plain,(
% 34.50/4.75    ( ! [X14,X12,X13,X11] : (~r2_hidden(sK3(X14,X11,k5_xboole_0(X12,X13)),X13) | ~r2_hidden(sK3(X14,X11,k5_xboole_0(X12,X13)),X11) | r2_hidden(sK3(X14,X11,k5_xboole_0(X12,X13)),X14) | r2_hidden(sK3(X14,X11,k5_xboole_0(X12,X13)),X12) | k5_xboole_0(X11,k5_xboole_0(X12,X13)) = X14) )),
% 34.50/4.75    inference(resolution,[],[f18,f22])).
% 34.50/4.75  fof(f22,plain,(
% 34.50/4.75    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 34.50/4.75    inference(cnf_transformation,[],[f13])).
% 34.50/4.75  fof(f18,plain,(
% 34.50/4.75    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | k5_xboole_0(X1,X2) = X0 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 34.50/4.75    inference(cnf_transformation,[],[f12])).
% 34.50/4.75  fof(f6336,plain,(
% 34.50/4.75    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X5 | ~r2_hidden(sK3(X5,X4,k5_xboole_0(X5,X4)),X5) | ~r2_hidden(sK3(X5,X4,k5_xboole_0(X5,X4)),X4)) )),
% 34.50/4.75    inference(resolution,[],[f6324,f20])).
% 34.50/4.75  fof(f20,plain,(
% 34.50/4.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 34.50/4.75    inference(cnf_transformation,[],[f13])).
% 34.50/4.75  fof(f6324,plain,(
% 34.50/4.75    ( ! [X10,X11] : (r2_hidden(sK3(X11,X10,k5_xboole_0(X11,X10)),k5_xboole_0(X11,X10)) | k5_xboole_0(X10,k5_xboole_0(X11,X10)) = X11) )),
% 34.50/4.75    inference(subsumption_resolution,[],[f6318,f6059])).
% 34.50/4.75  fof(f6059,plain,(
% 34.50/4.75    ( ! [X4,X5,X3] : (r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X5) | r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X3) | k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X3) )),
% 34.50/4.75    inference(subsumption_resolution,[],[f5949,f79])).
% 34.50/4.75  fof(f5949,plain,(
% 34.50/4.75    ( ! [X4,X5,X3] : (r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X4) | r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X5) | r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X3) | k5_xboole_0(X4,k5_xboole_0(X5,X4)) = X3) )),
% 34.50/4.75    inference(factoring,[],[f38])).
% 34.50/4.75  fof(f6318,plain,(
% 34.50/4.75    ( ! [X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X11,X10)) = X11 | r2_hidden(sK3(X11,X10,k5_xboole_0(X11,X10)),k5_xboole_0(X11,X10)) | ~r2_hidden(sK3(X11,X10,k5_xboole_0(X11,X10)),X11)) )),
% 34.50/4.75    inference(duplicate_literal_removal,[],[f6304])).
% 34.50/4.75  fof(f6304,plain,(
% 34.50/4.75    ( ! [X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X11,X10)) = X11 | r2_hidden(sK3(X11,X10,k5_xboole_0(X11,X10)),k5_xboole_0(X11,X10)) | k5_xboole_0(X10,k5_xboole_0(X11,X10)) = X11 | ~r2_hidden(sK3(X11,X10,k5_xboole_0(X11,X10)),X11)) )),
% 34.50/4.75    inference(resolution,[],[f6286,f15])).
% 34.50/4.75  fof(f15,plain,(
% 34.50/4.75    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k5_xboole_0(X1,X2) = X0 | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 34.50/4.75    inference(cnf_transformation,[],[f12])).
% 34.50/4.75  fof(f6286,plain,(
% 34.50/4.75    ( ! [X2,X1] : (r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X1) | k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 34.50/4.75    inference(subsumption_resolution,[],[f6283,f38])).
% 34.50/4.75  fof(f6283,plain,(
% 34.50/4.75    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 | ~r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X2) | r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X1)) )),
% 34.50/4.75    inference(duplicate_literal_removal,[],[f6257])).
% 34.50/4.75  fof(f6257,plain,(
% 34.50/4.75    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 | k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 | ~r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X2) | r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X1) | r2_hidden(sK3(X2,X1,k5_xboole_0(X2,X1)),X1)) )),
% 34.50/4.75    inference(resolution,[],[f6180,f34])).
% 34.50/4.75  fof(f6180,plain,(
% 34.50/4.75    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,k5_xboole_0(X0,X1)),X0) | k5_xboole_0(X1,k5_xboole_0(X0,X1)) = X0) )),
% 34.50/4.75    inference(factoring,[],[f6059])).
% 34.50/4.76  fof(f9989,plain,(
% 34.50/4.76    ( ! [X6,X7] : (k5_xboole_0(X6,k5_xboole_0(X6,X7)) = X7) )),
% 34.50/4.76    inference(subsumption_resolution,[],[f9988,f6061])).
% 34.50/4.76  fof(f6061,plain,(
% 34.50/4.76    ( ! [X10,X11,X9] : (r2_hidden(sK3(X9,X10,k5_xboole_0(X10,X11)),X11) | r2_hidden(sK3(X9,X10,k5_xboole_0(X10,X11)),X9) | k5_xboole_0(X10,k5_xboole_0(X10,X11)) = X9) )),
% 34.50/4.76    inference(subsumption_resolution,[],[f5951,f80])).
% 34.50/4.76  fof(f80,plain,(
% 34.50/4.76    ( ! [X17,X15,X18,X16] : (~r2_hidden(sK3(X18,X15,k5_xboole_0(X16,X17)),X16) | ~r2_hidden(sK3(X18,X15,k5_xboole_0(X16,X17)),X15) | r2_hidden(sK3(X18,X15,k5_xboole_0(X16,X17)),X18) | r2_hidden(sK3(X18,X15,k5_xboole_0(X16,X17)),X17) | k5_xboole_0(X15,k5_xboole_0(X16,X17)) = X18) )),
% 34.50/4.76    inference(resolution,[],[f18,f21])).
% 34.50/4.76  fof(f5951,plain,(
% 34.50/4.76    ( ! [X10,X11,X9] : (r2_hidden(sK3(X9,X10,k5_xboole_0(X10,X11)),X11) | r2_hidden(sK3(X9,X10,k5_xboole_0(X10,X11)),X10) | r2_hidden(sK3(X9,X10,k5_xboole_0(X10,X11)),X9) | k5_xboole_0(X10,k5_xboole_0(X10,X11)) = X9) )),
% 34.50/4.76    inference(factoring,[],[f38])).
% 34.50/4.76  fof(f9988,plain,(
% 34.50/4.76    ( ! [X6,X7] : (k5_xboole_0(X6,k5_xboole_0(X6,X7)) = X7 | ~r2_hidden(sK3(X7,X6,k5_xboole_0(X6,X7)),X7)) )),
% 34.50/4.76    inference(subsumption_resolution,[],[f9972,f33])).
% 34.50/4.76  fof(f33,plain,(
% 34.50/4.76    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK3(X0,X1,k5_xboole_0(X2,X3)),X3) | k5_xboole_0(X1,k5_xboole_0(X2,X3)) = X0 | ~r2_hidden(sK3(X0,X1,k5_xboole_0(X2,X3)),X0) | r2_hidden(sK3(X0,X1,k5_xboole_0(X2,X3)),X2) | r2_hidden(sK3(X0,X1,k5_xboole_0(X2,X3)),X1)) )),
% 34.50/4.76    inference(resolution,[],[f16,f22])).
% 34.50/4.76  fof(f9972,plain,(
% 34.50/4.76    ( ! [X6,X7] : (k5_xboole_0(X6,k5_xboole_0(X6,X7)) = X7 | ~r2_hidden(sK3(X7,X6,k5_xboole_0(X6,X7)),X6) | ~r2_hidden(sK3(X7,X6,k5_xboole_0(X6,X7)),X7)) )),
% 34.50/4.76    inference(resolution,[],[f9741,f20])).
% 34.50/4.76  fof(f9741,plain,(
% 34.50/4.76    ( ! [X8,X9] : (r2_hidden(sK3(X9,X8,k5_xboole_0(X8,X9)),k5_xboole_0(X8,X9)) | k5_xboole_0(X8,k5_xboole_0(X8,X9)) = X9) )),
% 34.50/4.76    inference(subsumption_resolution,[],[f9735,f7763])).
% 34.50/4.76  fof(f7763,plain,(
% 34.50/4.76    ( ! [X19,X17,X20,X18] : (r2_hidden(sK3(X19,X18,X20),k5_xboole_0(X18,X17)) | r2_hidden(sK3(X19,X18,X20),X20) | r2_hidden(sK3(X19,X18,X20),X19) | r2_hidden(sK3(X19,X18,X20),X17) | k5_xboole_0(X18,X20) = X19) )),
% 34.50/4.76    inference(superposition,[],[f42,f6351])).
% 34.50/4.76  fof(f42,plain,(
% 34.50/4.76    ( ! [X12,X10,X11,X9] : (r2_hidden(sK3(X9,k5_xboole_0(X10,X11),X12),X12) | r2_hidden(sK3(X9,k5_xboole_0(X10,X11),X12),X11) | r2_hidden(sK3(X9,k5_xboole_0(X10,X11),X12),X10) | r2_hidden(sK3(X9,k5_xboole_0(X10,X11),X12),X9) | k5_xboole_0(k5_xboole_0(X10,X11),X12) = X9) )),
% 34.50/4.76    inference(resolution,[],[f17,f19])).
% 34.50/4.76  fof(f9735,plain,(
% 34.50/4.76    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(X8,X9)) = X9 | r2_hidden(sK3(X9,X8,k5_xboole_0(X8,X9)),k5_xboole_0(X8,X9)) | ~r2_hidden(sK3(X9,X8,k5_xboole_0(X8,X9)),X9)) )),
% 34.50/4.76    inference(duplicate_literal_removal,[],[f9717])).
% 34.50/4.76  fof(f9717,plain,(
% 34.50/4.76    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(X8,X9)) = X9 | r2_hidden(sK3(X9,X8,k5_xboole_0(X8,X9)),k5_xboole_0(X8,X9)) | k5_xboole_0(X8,k5_xboole_0(X8,X9)) = X9 | ~r2_hidden(sK3(X9,X8,k5_xboole_0(X8,X9)),X9)) )),
% 34.50/4.76    inference(resolution,[],[f9328,f15])).
% 34.50/4.76  fof(f9328,plain,(
% 34.50/4.76    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,k5_xboole_0(X1,X0)),X1) | k5_xboole_0(X1,k5_xboole_0(X1,X0)) = X0) )),
% 34.50/4.76    inference(factoring,[],[f6060])).
% 34.50/4.76  fof(f6060,plain,(
% 34.50/4.76    ( ! [X6,X8,X7] : (r2_hidden(sK3(X6,X7,k5_xboole_0(X8,X6)),X8) | r2_hidden(sK3(X6,X7,k5_xboole_0(X8,X6)),X7) | k5_xboole_0(X7,k5_xboole_0(X8,X6)) = X6) )),
% 34.50/4.76    inference(subsumption_resolution,[],[f5950,f33])).
% 34.50/4.76  fof(f5950,plain,(
% 34.50/4.76    ( ! [X6,X8,X7] : (r2_hidden(sK3(X6,X7,k5_xboole_0(X8,X6)),X6) | r2_hidden(sK3(X6,X7,k5_xboole_0(X8,X6)),X8) | r2_hidden(sK3(X6,X7,k5_xboole_0(X8,X6)),X7) | k5_xboole_0(X7,k5_xboole_0(X8,X6)) = X6) )),
% 34.50/4.76    inference(factoring,[],[f38])).
% 34.50/4.76  fof(f14,plain,(
% 34.50/4.76    k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 34.50/4.76    inference(cnf_transformation,[],[f9])).
% 34.50/4.76  fof(f9,plain,(
% 34.50/4.76    k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 34.50/4.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8])).
% 34.50/4.76  fof(f8,plain,(
% 34.50/4.76    ? [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) != k5_xboole_0(X0,k5_xboole_0(X1,X2)) => k5_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))),
% 34.50/4.76    introduced(choice_axiom,[])).
% 34.50/4.76  fof(f5,plain,(
% 34.50/4.76    ? [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) != k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 34.50/4.76    inference(ennf_transformation,[],[f4])).
% 34.50/4.76  fof(f4,negated_conjecture,(
% 34.50/4.76    ~! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 34.50/4.76    inference(negated_conjecture,[],[f3])).
% 34.50/4.76  fof(f3,conjecture,(
% 34.50/4.76    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 34.50/4.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 34.50/4.76  fof(f97888,plain,(
% 34.50/4.76    k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | ~spl4_3),
% 34.50/4.76    inference(resolution,[],[f94482,f18])).
% 34.50/4.76  fof(f94482,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) | ~spl4_3),
% 34.50/4.76    inference(avatar_component_clause,[],[f94481])).
% 34.50/4.76  fof(f94481,plain,(
% 34.50/4.76    spl4_3 <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))),
% 34.50/4.76    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 34.50/4.76  fof(f98871,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | (~spl4_3 | ~spl4_4 | spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f98828,f97614,f20])).
% 34.50/4.76  fof(f97614,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (~spl4_4 | spl4_5)),
% 34.50/4.76    inference(forward_demodulation,[],[f97595,f10010])).
% 34.50/4.76  fof(f97595,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,sK1)) | (~spl4_4 | spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f95540,f94487,f21])).
% 34.50/4.76  fof(f95540,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1) | spl4_5),
% 34.50/4.76    inference(avatar_component_clause,[],[f95538])).
% 34.50/4.76  fof(f95538,plain,(
% 34.50/4.76    spl4_5 <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1)),
% 34.50/4.76    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 34.50/4.76  fof(f98828,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) | (~spl4_3 | spl4_5)),
% 34.50/4.76    inference(forward_demodulation,[],[f98827,f6351])).
% 34.50/4.76  fof(f98827,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | (~spl4_3 | spl4_5)),
% 34.50/4.76    inference(forward_demodulation,[],[f98812,f10010])).
% 34.50/4.76  fof(f98812,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)) | (~spl4_3 | spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f95540,f94482,f21])).
% 34.50/4.76  fof(f98780,plain,(
% 34.50/4.76    spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 34.50/4.76    inference(avatar_contradiction_clause,[],[f98779])).
% 34.50/4.76  fof(f98779,plain,(
% 34.50/4.76    $false | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 34.50/4.76    inference(subsumption_resolution,[],[f98768,f98762])).
% 34.50/4.76  fof(f98762,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (spl4_1 | ~spl4_3 | ~spl4_5)),
% 34.50/4.76    inference(subsumption_resolution,[],[f94445,f97893])).
% 34.50/4.76  fof(f97893,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) | (~spl4_3 | ~spl4_5)),
% 34.50/4.76    inference(forward_demodulation,[],[f97892,f6351])).
% 34.50/4.76  fof(f97892,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | (~spl4_3 | ~spl4_5)),
% 34.50/4.76    inference(forward_demodulation,[],[f97886,f10010])).
% 34.50/4.76  fof(f97886,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)) | (~spl4_3 | ~spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f95539,f94482,f20])).
% 34.50/4.76  fof(f95539,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1) | ~spl4_5),
% 34.50/4.76    inference(avatar_component_clause,[],[f95538])).
% 34.50/4.76  fof(f94445,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) | spl4_1),
% 34.50/4.76    inference(subsumption_resolution,[],[f94422,f10451])).
% 34.50/4.76  fof(f94422,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)) | spl4_1),
% 34.50/4.76    inference(resolution,[],[f94392,f8423])).
% 34.50/4.76  fof(f8423,plain,(
% 34.50/4.76    ( ! [X70,X72,X71,X73] : (r2_hidden(sK3(k5_xboole_0(X70,X71),X72,X73),k5_xboole_0(X72,X73)) | r2_hidden(sK3(k5_xboole_0(X70,X71),X72,X73),X71) | r2_hidden(sK3(k5_xboole_0(X70,X71),X72,X73),X70) | k5_xboole_0(X70,X71) = k5_xboole_0(X72,X73)) )),
% 34.50/4.76    inference(resolution,[],[f7233,f19])).
% 34.50/4.76  fof(f7233,plain,(
% 34.50/4.76    ( ! [X35,X33,X34] : (r2_hidden(sK3(X35,X33,X34),k5_xboole_0(X33,X34)) | r2_hidden(sK3(X35,X33,X34),X35) | k5_xboole_0(X33,X34) = X35) )),
% 34.50/4.76    inference(superposition,[],[f6357,f6389])).
% 34.50/4.76  fof(f6389,plain,(
% 34.50/4.76    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) )),
% 34.50/4.76    inference(superposition,[],[f6351,f6351])).
% 34.50/4.76  fof(f6357,plain,(
% 34.50/4.76    ( ! [X4,X5,X3] : (r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X5) | r2_hidden(sK3(X3,X4,k5_xboole_0(X5,X4)),X3) | X3 = X5) )),
% 34.50/4.76    inference(backward_demodulation,[],[f6059,f6351])).
% 34.50/4.76  fof(f94392,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))) | spl4_1),
% 34.50/4.76    inference(avatar_component_clause,[],[f94390])).
% 34.50/4.76  fof(f94390,plain,(
% 34.50/4.76    spl4_1 <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)))),
% 34.50/4.76    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 34.50/4.76  fof(f98768,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (~spl4_4 | ~spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f95539,f94487,f20])).
% 34.50/4.76  fof(f98725,plain,(
% 34.50/4.76    spl4_2 | ~spl4_5 | ~spl4_6),
% 34.50/4.76    inference(avatar_contradiction_clause,[],[f98724])).
% 34.50/4.76  fof(f98724,plain,(
% 34.50/4.76    $false | (spl4_2 | ~spl4_5 | ~spl4_6)),
% 34.50/4.76    inference(subsumption_resolution,[],[f98708,f97703])).
% 34.50/4.76  fof(f97703,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (spl4_2 | ~spl4_6)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f94396,f95544,f21])).
% 34.50/4.76  fof(f95544,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) | ~spl4_6),
% 34.50/4.76    inference(avatar_component_clause,[],[f95542])).
% 34.50/4.76  fof(f95542,plain,(
% 34.50/4.76    spl4_6 <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0)),
% 34.50/4.76    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 34.50/4.76  fof(f94396,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | spl4_2),
% 34.50/4.76    inference(avatar_component_clause,[],[f94394])).
% 34.50/4.76  fof(f94394,plain,(
% 34.50/4.76    spl4_2 <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))),
% 34.50/4.76    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 34.50/4.76  fof(f98708,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (spl4_2 | ~spl4_5 | ~spl4_6)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f95539,f98648,f20])).
% 34.50/4.76  fof(f98648,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | (spl4_2 | ~spl4_5 | ~spl4_6)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f10451,f95539,f94396,f95544,f37])).
% 34.50/4.76  fof(f37,plain,(
% 34.50/4.76    ( ! [X6,X8,X7,X5] : (~r2_hidden(sK3(X5,X6,k5_xboole_0(X7,X8)),X8) | r2_hidden(sK3(X5,X6,k5_xboole_0(X7,X8)),X5) | k5_xboole_0(X6,k5_xboole_0(X7,X8)) = X5 | ~r2_hidden(sK3(X5,X6,k5_xboole_0(X7,X8)),X7) | r2_hidden(sK3(X5,X6,k5_xboole_0(X7,X8)),X6)) )),
% 34.50/4.76    inference(resolution,[],[f17,f20])).
% 34.50/4.76  fof(f98643,plain,(
% 34.50/4.76    spl4_2 | ~spl4_3 | ~spl4_5),
% 34.50/4.76    inference(avatar_contradiction_clause,[],[f98642])).
% 34.50/4.76  fof(f98642,plain,(
% 34.50/4.76    $false | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 34.50/4.76    inference(subsumption_resolution,[],[f98605,f98548])).
% 34.50/4.76  fof(f98548,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f95539,f97894,f21])).
% 34.50/4.76  fof(f97894,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | (spl4_2 | ~spl4_3)),
% 34.50/4.76    inference(forward_demodulation,[],[f97884,f6351])).
% 34.50/4.76  fof(f97884,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)))) | (spl4_2 | ~spl4_3)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f97400,f94482,f20])).
% 34.50/4.76  fof(f97400,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))) | spl4_2),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f76871,f94396,f19])).
% 34.50/4.76  fof(f76871,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))))),
% 34.50/4.76    inference(forward_demodulation,[],[f76764,f10010])).
% 34.50/4.76  fof(f76764,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))))),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f10451,f75402])).
% 34.50/4.76  fof(f75402,plain,(
% 34.50/4.76    ( ! [X14,X15,X13] : (r2_hidden(sK3(X15,X14,X13),k5_xboole_0(k5_xboole_0(X14,X13),X15)) | k5_xboole_0(X14,X13) = X15) )),
% 34.50/4.76    inference(superposition,[],[f75284,f6351])).
% 34.50/4.76  fof(f75284,plain,(
% 34.50/4.76    ( ! [X161,X162,X160] : (r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),k5_xboole_0(X162,X160)) | X160 = X162) )),
% 34.50/4.76    inference(subsumption_resolution,[],[f75283,f75278])).
% 34.50/4.76  fof(f75278,plain,(
% 34.50/4.76    ( ! [X64,X62,X63] : (r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),k5_xboole_0(X64,X62)) | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X63) | X62 = X64) )),
% 34.50/4.76    inference(duplicate_literal_removal,[],[f75277])).
% 34.50/4.76  fof(f75277,plain,(
% 34.50/4.76    ( ! [X64,X62,X63] : (X62 = X64 | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),k5_xboole_0(X64,X62)) | X62 = X64 | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X63)) )),
% 34.50/4.76    inference(forward_demodulation,[],[f75276,f9989])).
% 34.50/4.76  fof(f75276,plain,(
% 34.50/4.76    ( ! [X64,X62,X63] : (k5_xboole_0(X63,k5_xboole_0(X63,X64)) = X62 | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),k5_xboole_0(X64,X62)) | X62 = X64 | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X63)) )),
% 34.50/4.76    inference(forward_demodulation,[],[f75275,f10010])).
% 34.50/4.76  fof(f75275,plain,(
% 34.50/4.76    ( ! [X64,X62,X63] : (r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),k5_xboole_0(X64,X62)) | X62 = X64 | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X63) | k5_xboole_0(k5_xboole_0(X63,X64),X63) = X62) )),
% 34.50/4.76    inference(subsumption_resolution,[],[f75076,f66071])).
% 34.50/4.76  fof(f66071,plain,(
% 34.50/4.76    ( ! [X14,X15,X13] : (r2_hidden(sK3(X15,k5_xboole_0(X14,X13),X14),k5_xboole_0(X13,X15)) | r2_hidden(sK3(X15,k5_xboole_0(X14,X13),X14),X15) | X13 = X15) )),
% 34.50/4.76    inference(superposition,[],[f65825,f6351])).
% 34.50/4.76  fof(f65825,plain,(
% 34.50/4.76    ( ! [X14,X15,X13] : (r2_hidden(sK3(X13,X15,k5_xboole_0(X14,X15)),k5_xboole_0(X14,X13)) | r2_hidden(sK3(X13,X15,k5_xboole_0(X14,X15)),X13) | X13 = X14) )),
% 34.50/4.76    inference(superposition,[],[f61732,f6351])).
% 34.50/4.76  fof(f61732,plain,(
% 34.50/4.76    ( ! [X88,X87,X86] : (r2_hidden(sK3(X86,X87,k5_xboole_0(k5_xboole_0(X86,X88),X87)),X88) | r2_hidden(sK3(X86,X87,k5_xboole_0(k5_xboole_0(X86,X88),X87)),X86) | k5_xboole_0(X86,X88) = X86) )),
% 34.50/4.76    inference(duplicate_literal_removal,[],[f61698])).
% 34.50/4.76  fof(f61698,plain,(
% 34.50/4.76    ( ! [X88,X87,X86] : (r2_hidden(sK3(X86,X87,k5_xboole_0(k5_xboole_0(X86,X88),X87)),X88) | k5_xboole_0(X86,X88) = X86 | r2_hidden(sK3(X86,X87,k5_xboole_0(k5_xboole_0(X86,X88),X87)),X86) | r2_hidden(sK3(X86,X87,k5_xboole_0(k5_xboole_0(X86,X88),X87)),X88)) )),
% 34.50/4.76    inference(resolution,[],[f61503,f19])).
% 34.50/4.76  fof(f61503,plain,(
% 34.50/4.76    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,k5_xboole_0(k5_xboole_0(X0,X2),X1)),k5_xboole_0(X0,X2)) | r2_hidden(sK3(X0,X1,k5_xboole_0(k5_xboole_0(X0,X2),X1)),X2) | k5_xboole_0(X0,X2) = X0) )),
% 34.50/4.76    inference(factoring,[],[f58939])).
% 34.50/4.76  fof(f58939,plain,(
% 34.50/4.76    ( ! [X19,X17,X20,X18] : (r2_hidden(sK3(X19,X17,k5_xboole_0(X18,X17)),k5_xboole_0(X19,X20)) | r2_hidden(sK3(X19,X17,k5_xboole_0(X18,X17)),X18) | r2_hidden(sK3(X19,X17,k5_xboole_0(X18,X17)),X20) | X18 = X19) )),
% 34.50/4.76    inference(superposition,[],[f58512,f6351])).
% 34.50/4.76  fof(f58512,plain,(
% 34.50/4.76    ( ! [X19,X17,X20,X18] : (r2_hidden(sK3(X18,X19,X20),k5_xboole_0(X19,X20)) | r2_hidden(sK3(X18,X19,X20),k5_xboole_0(X18,X17)) | r2_hidden(sK3(X18,X19,X20),X17) | k5_xboole_0(X19,X20) = X18) )),
% 34.50/4.76    inference(superposition,[],[f8423,f6351])).
% 34.50/4.76  fof(f75076,plain,(
% 34.50/4.76    ( ! [X64,X62,X63] : (r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),k5_xboole_0(X64,X62)) | X62 = X64 | r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X63) | k5_xboole_0(k5_xboole_0(X63,X64),X63) = X62 | ~r2_hidden(sK3(X62,k5_xboole_0(X63,X64),X63),X62)) )),
% 34.50/4.76    inference(resolution,[],[f69741,f15])).
% 34.50/4.76  fof(f69741,plain,(
% 34.50/4.76    ( ! [X14,X15,X13] : (r2_hidden(sK3(X15,k5_xboole_0(X14,X13),X14),k5_xboole_0(X14,X13)) | r2_hidden(sK3(X15,k5_xboole_0(X14,X13),X14),k5_xboole_0(X13,X15)) | X13 = X15) )),
% 34.50/4.76    inference(superposition,[],[f69224,f6351])).
% 34.50/4.76  fof(f69224,plain,(
% 34.50/4.76    ( ! [X14,X15,X13] : (r2_hidden(sK3(X13,X15,k5_xboole_0(X14,X15)),k5_xboole_0(X14,X13)) | r2_hidden(sK3(X13,X15,k5_xboole_0(X14,X15)),X15) | X13 = X14) )),
% 34.50/4.76    inference(superposition,[],[f61748,f6351])).
% 34.50/4.76  fof(f61748,plain,(
% 34.50/4.76    ( ! [X23,X21,X22] : (r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X23) | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22) | k5_xboole_0(X21,X23) = X21) )),
% 34.50/4.76    inference(duplicate_literal_removal,[],[f61747])).
% 34.50/4.76  fof(f61747,plain,(
% 34.50/4.76    ( ! [X23,X21,X22] : (k5_xboole_0(X21,X23) = X21 | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X23) | k5_xboole_0(X21,X23) = X21 | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22)) )),
% 34.50/4.76    inference(forward_demodulation,[],[f61746,f6351])).
% 34.50/4.76  fof(f61746,plain,(
% 34.50/4.76    ( ! [X23,X21,X22] : (r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X23) | k5_xboole_0(X21,X23) = X21 | k5_xboole_0(X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)) = X21 | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22)) )),
% 34.50/4.76    inference(subsumption_resolution,[],[f61736,f5899])).
% 34.50/4.76  fof(f5899,plain,(
% 34.50/4.76    ( ! [X80,X78,X81,X79,X82] : (r2_hidden(sK3(X78,X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)),X82) | r2_hidden(sK3(X78,X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)),X81) | r2_hidden(sK3(X78,X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)),X80) | r2_hidden(sK3(X78,X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)),X79) | r2_hidden(sK3(X78,X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)),X78) | k5_xboole_0(X79,k5_xboole_0(k5_xboole_0(X80,X81),X82)) = X78) )),
% 34.50/4.76    inference(resolution,[],[f38,f19])).
% 34.50/4.76  fof(f61736,plain,(
% 34.50/4.76    ( ! [X23,X21,X22] : (r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X23) | k5_xboole_0(X21,X23) = X21 | k5_xboole_0(X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)) = X21 | ~r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X21) | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22)) )),
% 34.50/4.76    inference(duplicate_literal_removal,[],[f61671])).
% 34.50/4.76  fof(f61671,plain,(
% 34.50/4.76    ( ! [X23,X21,X22] : (r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X23) | k5_xboole_0(X21,X23) = X21 | k5_xboole_0(X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)) = X21 | ~r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X21) | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22) | r2_hidden(sK3(X21,X22,k5_xboole_0(k5_xboole_0(X21,X23),X22)),X22)) )),
% 34.50/4.76    inference(resolution,[],[f61503,f34])).
% 34.50/4.76  fof(f75283,plain,(
% 34.50/4.76    ( ! [X161,X162,X160] : (r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),k5_xboole_0(X162,X160)) | X160 = X162 | ~r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),X161)) )),
% 34.50/4.76    inference(subsumption_resolution,[],[f75118,f59253])).
% 34.50/4.76  fof(f59253,plain,(
% 34.50/4.76    ( ! [X57,X54,X56,X55] : (r2_hidden(sK3(X56,k5_xboole_0(X54,X55),X54),X55) | r2_hidden(sK3(X56,k5_xboole_0(X54,X55),X54),k5_xboole_0(X57,X56)) | r2_hidden(sK3(X56,k5_xboole_0(X54,X55),X54),X57) | X55 = X56) )),
% 34.50/4.76    inference(superposition,[],[f58513,f6389])).
% 34.50/4.76  fof(f58513,plain,(
% 34.50/4.76    ( ! [X24,X23,X21,X22] : (r2_hidden(sK3(X22,X23,X24),k5_xboole_0(X23,X24)) | r2_hidden(sK3(X22,X23,X24),k5_xboole_0(X21,X22)) | r2_hidden(sK3(X22,X23,X24),X21) | k5_xboole_0(X23,X24) = X22) )),
% 34.50/4.76    inference(superposition,[],[f8423,f9989])).
% 34.50/4.76  fof(f75118,plain,(
% 34.50/4.76    ( ! [X161,X162,X160] : (r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),k5_xboole_0(X162,X160)) | X160 = X162 | ~r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),X161) | ~r2_hidden(sK3(X160,k5_xboole_0(X161,X162),X161),X162)) )),
% 34.50/4.76    inference(resolution,[],[f69741,f20])).
% 34.50/4.76  fof(f98605,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (spl4_2 | ~spl4_3 | ~spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f94396,f97893,f22])).
% 34.50/4.76  fof(f97807,plain,(
% 34.50/4.76    spl4_2 | spl4_5 | ~spl4_6),
% 34.50/4.76    inference(avatar_contradiction_clause,[],[f97806])).
% 34.50/4.76  fof(f97806,plain,(
% 34.50/4.76    $false | (spl4_2 | spl4_5 | ~spl4_6)),
% 34.50/4.76    inference(subsumption_resolution,[],[f97783,f97703])).
% 34.50/4.76  fof(f97783,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (spl4_2 | spl4_5 | ~spl4_6)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f95540,f97692,f19])).
% 34.50/4.76  fof(f97692,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | (spl4_2 | spl4_5 | ~spl4_6)),
% 34.50/4.76    inference(subsumption_resolution,[],[f97691,f10451])).
% 34.50/4.76  fof(f97691,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)) | (spl4_2 | spl4_5 | ~spl4_6)),
% 34.50/4.76    inference(subsumption_resolution,[],[f97690,f95540])).
% 34.50/4.76  fof(f97690,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1) | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)) | (spl4_2 | ~spl4_6)),
% 34.50/4.76    inference(subsumption_resolution,[],[f95737,f94396])).
% 34.50/4.76  fof(f95737,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1) | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)) | ~spl4_6),
% 34.50/4.76    inference(resolution,[],[f95544,f80])).
% 34.50/4.76  fof(f97686,plain,(
% 34.50/4.76    spl4_2 | ~spl4_4 | spl4_5),
% 34.50/4.76    inference(avatar_contradiction_clause,[],[f97685])).
% 34.50/4.76  fof(f97685,plain,(
% 34.50/4.76    $false | (spl4_2 | ~spl4_4 | spl4_5)),
% 34.50/4.76    inference(subsumption_resolution,[],[f97647,f97614])).
% 34.50/4.76  fof(f97647,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (spl4_2 | ~spl4_4 | spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f94396,f97627,f22])).
% 34.50/4.76  fof(f97627,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) | (spl4_2 | ~spl4_4 | spl4_5)),
% 34.50/4.76    inference(forward_demodulation,[],[f97571,f6351])).
% 34.50/4.76  fof(f97571,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | (spl4_2 | ~spl4_4 | spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f10451,f95540,f94396,f94487,f10977])).
% 34.50/4.76  fof(f10977,plain,(
% 34.50/4.76    ( ! [X24,X23,X21,X22] : (~r2_hidden(sK3(X23,X24,X22),k5_xboole_0(X21,X22)) | ~r2_hidden(sK3(X23,X24,X22),X24) | r2_hidden(sK3(X23,X24,X22),X23) | r2_hidden(sK3(X23,X24,X22),X21) | k5_xboole_0(X24,X22) = X23) )),
% 34.50/4.76    inference(superposition,[],[f79,f9989])).
% 34.50/4.76  fof(f97561,plain,(
% 34.50/4.76    spl4_4 | spl4_6 | spl4_2 | spl4_5),
% 34.50/4.76    inference(avatar_split_clause,[],[f97459,f95538,f94394,f95542,f94485])).
% 34.50/4.76  fof(f97459,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | (spl4_2 | spl4_5)),
% 34.50/4.76    inference(subsumption_resolution,[],[f97458,f10451])).
% 34.50/4.76  fof(f97458,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)) | (spl4_2 | spl4_5)),
% 34.50/4.76    inference(subsumption_resolution,[],[f97401,f95540])).
% 34.50/4.76  fof(f97401,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1) | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)) | spl4_2),
% 34.50/4.76    inference(resolution,[],[f94396,f38])).
% 34.50/4.76  fof(f95833,plain,(
% 34.50/4.76    spl4_1 | spl4_3 | ~spl4_6),
% 34.50/4.76    inference(avatar_contradiction_clause,[],[f95832])).
% 34.50/4.76  fof(f95832,plain,(
% 34.50/4.76    $false | (spl4_1 | spl4_3 | ~spl4_6)),
% 34.50/4.76    inference(subsumption_resolution,[],[f95831,f95736])).
% 34.50/4.76  fof(f95736,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (spl4_1 | ~spl4_6)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f94419,f95544,f20])).
% 34.50/4.76  fof(f94419,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | spl4_1),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f76871,f94392,f19])).
% 34.50/4.76  fof(f95831,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (spl4_1 | spl4_3 | ~spl4_6)),
% 34.50/4.76    inference(forward_demodulation,[],[f95767,f10010])).
% 34.50/4.76  fof(f95767,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,sK1)) | (spl4_1 | spl4_3 | ~spl4_6)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f10451,f94483,f94419,f95720,f6425])).
% 34.50/4.76  fof(f6425,plain,(
% 34.50/4.76    ( ! [X92,X90,X93,X91] : (~r2_hidden(sK3(X92,X91,X93),X92) | k5_xboole_0(X91,X93) = X92 | ~r2_hidden(sK3(X92,X91,X93),X90) | r2_hidden(sK3(X92,X91,X93),k5_xboole_0(X91,X90)) | r2_hidden(sK3(X92,X91,X93),X93)) )),
% 34.50/4.76    inference(superposition,[],[f32,f6351])).
% 34.50/4.76  fof(f32,plain,(
% 34.50/4.76    ( ! [X6,X4,X7,X5] : (~r2_hidden(sK3(X4,k5_xboole_0(X5,X6),X7),X5) | k5_xboole_0(k5_xboole_0(X5,X6),X7) = X4 | ~r2_hidden(sK3(X4,k5_xboole_0(X5,X6),X7),X4) | r2_hidden(sK3(X4,k5_xboole_0(X5,X6),X7),X6) | r2_hidden(sK3(X4,k5_xboole_0(X5,X6),X7),X7)) )),
% 34.50/4.76    inference(resolution,[],[f15,f21])).
% 34.50/4.76  fof(f95720,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1) | (spl4_3 | ~spl4_6)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f94483,f95544,f21])).
% 34.50/4.76  fof(f94483,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) | spl4_3),
% 34.50/4.76    inference(avatar_component_clause,[],[f94481])).
% 34.50/4.76  fof(f95699,plain,(
% 34.50/4.76    spl4_1 | spl4_3 | spl4_5),
% 34.50/4.76    inference(avatar_contradiction_clause,[],[f95698])).
% 34.50/4.76  fof(f95698,plain,(
% 34.50/4.76    $false | (spl4_1 | spl4_3 | spl4_5)),
% 34.50/4.76    inference(subsumption_resolution,[],[f95603,f95579])).
% 34.50/4.76  fof(f95579,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (spl4_1 | spl4_3 | spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f95172,f95540,f19])).
% 34.50/4.76  fof(f95172,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | (spl4_1 | spl4_3)),
% 34.50/4.76    inference(forward_demodulation,[],[f95157,f6351])).
% 34.50/4.76  fof(f95157,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)))) | (spl4_1 | spl4_3)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f94392,f94483,f19])).
% 34.50/4.76  fof(f95603,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)) | (spl4_1 | spl4_3 | spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f10451,f95540,f95584,f95172,f95584,f5945])).
% 34.50/4.76  fof(f5945,plain,(
% 34.50/4.76    ( ! [X70,X68,X66,X69,X67] : (r2_hidden(sK3(k5_xboole_0(X66,X67),X68,k5_xboole_0(X69,X70)),X70) | r2_hidden(sK3(k5_xboole_0(X66,X67),X68,k5_xboole_0(X69,X70)),X69) | r2_hidden(sK3(k5_xboole_0(X66,X67),X68,k5_xboole_0(X69,X70)),X68) | r2_hidden(sK3(k5_xboole_0(X66,X67),X68,k5_xboole_0(X69,X70)),X67) | r2_hidden(sK3(k5_xboole_0(X66,X67),X68,k5_xboole_0(X69,X70)),X66) | k5_xboole_0(X68,k5_xboole_0(X69,X70)) = k5_xboole_0(X66,X67)) )),
% 34.50/4.76    inference(resolution,[],[f38,f19])).
% 34.50/4.76  fof(f95584,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) | (spl4_3 | spl4_5)),
% 34.50/4.76    inference(forward_demodulation,[],[f95577,f6351])).
% 34.50/4.76  fof(f95577,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | (spl4_3 | spl4_5)),
% 34.50/4.76    inference(unit_resulting_resolution,[],[f94483,f95540,f19])).
% 34.50/4.76  fof(f95545,plain,(
% 34.50/4.76    ~spl4_5 | spl4_6 | spl4_3),
% 34.50/4.76    inference(avatar_split_clause,[],[f95169,f94481,f95542,f95538])).
% 34.50/4.76  fof(f95169,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK1) | spl4_3),
% 34.50/4.76    inference(resolution,[],[f94483,f22])).
% 34.50/4.76  fof(f94488,plain,(
% 34.50/4.76    ~spl4_3 | spl4_4 | spl4_1),
% 34.50/4.76    inference(avatar_split_clause,[],[f94428,f94390,f94485,f94481])).
% 34.50/4.76  fof(f94428,plain,(
% 34.50/4.76    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),sK2) | ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) | spl4_1),
% 34.50/4.76    inference(resolution,[],[f94392,f22])).
% 34.50/4.76  fof(f94397,plain,(
% 34.50/4.76    ~spl4_1 | ~spl4_2),
% 34.50/4.76    inference(avatar_split_clause,[],[f83061,f94394,f94390])).
% 34.50/4.76  fof(f83061,plain,(
% 34.50/4.76    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)),sK2,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)))),
% 34.50/4.76    inference(resolution,[],[f76871,f20])).
% 34.50/4.76  % SZS output end Proof for theBenchmark
% 34.50/4.76  % (6150)------------------------------
% 34.50/4.76  % (6150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 34.50/4.76  % (6150)Termination reason: Refutation
% 34.50/4.76  
% 34.50/4.76  % (6150)Memory used [KB]: 43240
% 34.50/4.76  % (6150)Time elapsed: 4.327 s
% 34.50/4.76  % (6150)------------------------------
% 34.50/4.76  % (6150)------------------------------
% 35.19/4.76  % (6142)Success in time 4.401 s
%------------------------------------------------------------------------------
