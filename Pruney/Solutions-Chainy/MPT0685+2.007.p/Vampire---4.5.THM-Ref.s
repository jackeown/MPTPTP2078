%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:35 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 294 expanded)
%              Number of leaves         :   13 (  78 expanded)
%              Depth                    :   17
%              Number of atoms          :  236 (1555 expanded)
%              Number of equality atoms :   78 ( 309 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f485,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f141,f484])).

fof(f484,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f140,f390])).

fof(f390,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,X3) ),
    inference(superposition,[],[f261,f193])).

fof(f193,plain,(
    ! [X6,X7] : k3_xboole_0(X7,X6) = k3_xboole_0(X6,k3_xboole_0(X7,X6)) ),
    inference(subsumption_resolution,[],[f187,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X1),X0)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f107,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f107,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X1
      | ~ r2_hidden(sK3(X0,X1,X1),X1)
      | ~ r2_hidden(sK3(X0,X1,X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X1
      | ~ r2_hidden(sK3(X0,X1,X1),X1)
      | ~ r2_hidden(sK3(X0,X1,X1),X0)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f93,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f36])).

fof(f187,plain,(
    ! [X6,X7] :
      ( k3_xboole_0(X7,X6) = k3_xboole_0(X6,k3_xboole_0(X7,X6))
      | r2_hidden(sK3(X6,k3_xboole_0(X7,X6),k3_xboole_0(X7,X6)),X6) ) ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,(
    ! [X6,X7] :
      ( k3_xboole_0(X7,X6) = k3_xboole_0(X6,k3_xboole_0(X7,X6))
      | k3_xboole_0(X7,X6) = k3_xboole_0(X6,k3_xboole_0(X7,X6))
      | r2_hidden(sK3(X6,k3_xboole_0(X7,X6),k3_xboole_0(X7,X6)),X6) ) ),
    inference(resolution,[],[f108,f89])).

fof(f89,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK3(X4,X5,k3_xboole_0(X6,X7)),X7)
      | k3_xboole_0(X6,X7) = k3_xboole_0(X4,X5)
      | r2_hidden(sK3(X4,X5,k3_xboole_0(X6,X7)),X4) ) ),
    inference(resolution,[],[f35,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f261,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f135,f203])).

fof(f203,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(subsumption_resolution,[],[f202,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X0),X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f102,f35])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r2_hidden(sK3(X0,X1,X0),X1)
      | ~ r2_hidden(sK3(X0,X1,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r2_hidden(sK3(X0,X1,X0),X1)
      | ~ r2_hidden(sK3(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f90,f37])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f35])).

fof(f202,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)
      | r2_hidden(sK3(k3_xboole_0(X0,X1),X0,k3_xboole_0(X0,X1)),X0) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)
      | r2_hidden(sK3(k3_xboole_0(X0,X1),X0,k3_xboole_0(X0,X1)),X0)
      | k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f91,f103])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(X0,X1,k3_xboole_0(X2,X3)),X2)
      | k3_xboole_0(X0,X1) = k3_xboole_0(X2,X3)
      | r2_hidden(sK3(X0,X1,k3_xboole_0(X2,X3)),X1) ) ),
    inference(resolution,[],[f36,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f135,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X2,X0),X1) ),
    inference(forward_demodulation,[],[f134,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f70,f42])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f70,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(subsumption_resolution,[],[f67,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f66,f31])).

fof(f31,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f65,f41])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k10_relat_1(X1,X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f39,f42])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f134,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k10_relat_1(k6_relat_1(X0),X2),X1) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f133,f71])).

fof(f133,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k10_relat_1(k6_relat_1(X0),X2),X1) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) ),
    inference(subsumption_resolution,[],[f129,f41])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k10_relat_1(k6_relat_1(X0),X2),X1) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f128,f61])).

fof(f61,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(subsumption_resolution,[],[f59,f41])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X1),X0)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f40,f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f128,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k7_relat_1(X4,X3),X5) = k3_xboole_0(k10_relat_1(X4,X5),X3)
      | ~ v1_relat_1(X4) ) ),
    inference(forward_demodulation,[],[f83,f71])).

fof(f83,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f80,f41])).

fof(f80,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X4,X5,X3] :
      ( k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f30,f40])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(f140,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_3
  <=> k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) = k3_xboole_0(k10_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f141,plain,
    ( ~ spl4_3
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f136,f55,f50,f138])).

fof(f50,plain,
    ( spl4_1
  <=> k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f55,plain,
    ( spl4_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f136,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f131,f57])).

fof(f57,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f131,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(superposition,[],[f52,f128])).

fof(f52,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f53,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (31113)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (31121)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (31121)Refutation not found, incomplete strategy% (31121)------------------------------
% 0.22/0.51  % (31121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31121)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (31121)Memory used [KB]: 10746
% 0.22/0.51  % (31121)Time elapsed: 0.085 s
% 0.22/0.51  % (31121)------------------------------
% 0.22/0.51  % (31121)------------------------------
% 0.22/0.54  % (31108)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (31125)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (31122)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (31108)Refutation not found, incomplete strategy% (31108)------------------------------
% 0.22/0.55  % (31108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31114)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (31129)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (31122)Refutation not found, incomplete strategy% (31122)------------------------------
% 0.22/0.55  % (31122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31111)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (31114)Refutation not found, incomplete strategy% (31114)------------------------------
% 0.22/0.55  % (31114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (31103)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.56  % (31108)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (31108)Memory used [KB]: 10618
% 0.22/0.56  % (31108)Time elapsed: 0.125 s
% 0.22/0.56  % (31108)------------------------------
% 0.22/0.56  % (31108)------------------------------
% 0.22/0.56  % (31114)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (31114)Memory used [KB]: 6140
% 0.22/0.56  % (31114)Time elapsed: 0.003 s
% 0.22/0.56  % (31114)------------------------------
% 0.22/0.56  % (31114)------------------------------
% 0.22/0.56  % (31103)Refutation not found, incomplete strategy% (31103)------------------------------
% 0.22/0.56  % (31103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (31103)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (31103)Memory used [KB]: 6140
% 0.22/0.56  % (31103)Time elapsed: 0.122 s
% 0.22/0.56  % (31103)------------------------------
% 0.22/0.56  % (31103)------------------------------
% 0.22/0.56  % (31122)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (31122)Memory used [KB]: 1791
% 0.22/0.56  % (31122)Time elapsed: 0.111 s
% 0.22/0.56  % (31122)------------------------------
% 0.22/0.56  % (31122)------------------------------
% 0.22/0.56  % (31107)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (31116)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (31116)Refutation not found, incomplete strategy% (31116)------------------------------
% 0.22/0.56  % (31116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (31116)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (31116)Memory used [KB]: 10618
% 0.22/0.56  % (31116)Time elapsed: 0.147 s
% 0.22/0.56  % (31116)------------------------------
% 0.22/0.56  % (31116)------------------------------
% 0.22/0.57  % (31106)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (31128)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (31102)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (31102)Refutation not found, incomplete strategy% (31102)------------------------------
% 0.22/0.57  % (31102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (31102)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (31102)Memory used [KB]: 6140
% 0.22/0.57  % (31102)Time elapsed: 0.140 s
% 0.22/0.57  % (31102)------------------------------
% 0.22/0.57  % (31102)------------------------------
% 0.22/0.57  % (31099)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  % (31100)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (31119)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % (31112)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.58  % (31119)Refutation not found, incomplete strategy% (31119)------------------------------
% 0.22/0.58  % (31119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (31119)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (31119)Memory used [KB]: 10746
% 0.22/0.58  % (31119)Time elapsed: 0.144 s
% 0.22/0.58  % (31119)------------------------------
% 0.22/0.58  % (31119)------------------------------
% 0.22/0.58  % (31110)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % (31110)Refutation not found, incomplete strategy% (31110)------------------------------
% 0.22/0.58  % (31110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (31110)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (31110)Memory used [KB]: 10618
% 0.22/0.58  % (31110)Time elapsed: 0.159 s
% 0.22/0.58  % (31110)------------------------------
% 0.22/0.58  % (31110)------------------------------
% 0.22/0.58  % (31120)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.58  % (31115)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.58  % (31118)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.58  % (31126)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.59  % (31117)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.59  % (31127)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.59  % (31109)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.59  % (31109)Refutation not found, incomplete strategy% (31109)------------------------------
% 0.22/0.59  % (31109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (31109)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (31109)Memory used [KB]: 10618
% 0.22/0.59  % (31109)Time elapsed: 0.160 s
% 0.22/0.59  % (31109)------------------------------
% 0.22/0.59  % (31109)------------------------------
% 0.22/0.60  % (31101)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.61  % (31098)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.77/0.61  % (31105)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.77/0.62  % (31124)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.96/0.63  % (31098)Refutation not found, incomplete strategy% (31098)------------------------------
% 1.96/0.63  % (31098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.63  % (31098)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.63  
% 1.96/0.63  % (31098)Memory used [KB]: 1663
% 1.96/0.63  % (31098)Time elapsed: 0.128 s
% 1.96/0.63  % (31098)------------------------------
% 1.96/0.63  % (31098)------------------------------
% 1.96/0.64  % (31144)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.96/0.64  % (31144)Refutation not found, incomplete strategy% (31144)------------------------------
% 1.96/0.64  % (31144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.64  % (31144)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.64  
% 1.96/0.64  % (31144)Memory used [KB]: 6268
% 1.96/0.64  % (31144)Time elapsed: 0.089 s
% 1.96/0.64  % (31144)------------------------------
% 1.96/0.64  % (31144)------------------------------
% 2.19/0.68  % (31146)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.19/0.69  % (31150)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.19/0.70  % (31148)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.19/0.70  % (31147)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.19/0.71  % (31151)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.19/0.71  % (31152)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.19/0.72  % (31155)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.19/0.72  % (31153)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.19/0.72  % (31154)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.19/0.73  % (31154)Refutation not found, incomplete strategy% (31154)------------------------------
% 2.19/0.73  % (31154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.73  % (31154)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.73  
% 2.19/0.73  % (31154)Memory used [KB]: 1791
% 2.19/0.73  % (31154)Time elapsed: 0.107 s
% 2.19/0.73  % (31154)------------------------------
% 2.19/0.73  % (31154)------------------------------
% 2.19/0.73  % (31147)Refutation found. Thanks to Tanya!
% 2.19/0.73  % SZS status Theorem for theBenchmark
% 2.19/0.73  % SZS output start Proof for theBenchmark
% 2.19/0.73  fof(f485,plain,(
% 2.19/0.73    $false),
% 2.19/0.73    inference(avatar_sat_refutation,[],[f53,f58,f141,f484])).
% 2.19/0.73  fof(f484,plain,(
% 2.19/0.73    spl4_3),
% 2.19/0.73    inference(avatar_contradiction_clause,[],[f427])).
% 2.19/0.73  fof(f427,plain,(
% 2.19/0.73    $false | spl4_3),
% 2.19/0.73    inference(unit_resulting_resolution,[],[f140,f390])).
% 2.19/0.73  fof(f390,plain,(
% 2.19/0.73    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,X3)) )),
% 2.19/0.73    inference(superposition,[],[f261,f193])).
% 2.19/0.73  fof(f193,plain,(
% 2.19/0.73    ( ! [X6,X7] : (k3_xboole_0(X7,X6) = k3_xboole_0(X6,k3_xboole_0(X7,X6))) )),
% 2.19/0.73    inference(subsumption_resolution,[],[f187,f108])).
% 2.19/0.73  fof(f108,plain,(
% 2.19/0.73    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,X1),X0) | k3_xboole_0(X0,X1) = X1) )),
% 2.19/0.73    inference(subsumption_resolution,[],[f107,f36])).
% 2.19/0.73  fof(f36,plain,(
% 2.19/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | k3_xboole_0(X0,X1) = X2) )),
% 2.19/0.73    inference(cnf_transformation,[],[f27])).
% 2.19/0.73  fof(f27,plain,(
% 2.19/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.19/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 2.19/0.73  fof(f26,plain,(
% 2.19/0.73    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.19/0.73    introduced(choice_axiom,[])).
% 2.19/0.73  fof(f25,plain,(
% 2.19/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.19/0.73    inference(rectify,[],[f24])).
% 2.19/0.73  fof(f24,plain,(
% 2.19/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.19/0.73    inference(flattening,[],[f23])).
% 2.19/0.73  fof(f23,plain,(
% 2.19/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.19/0.73    inference(nnf_transformation,[],[f1])).
% 2.19/0.73  fof(f1,axiom,(
% 2.19/0.73    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.19/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.19/0.73  fof(f107,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X1 | ~r2_hidden(sK3(X0,X1,X1),X1) | ~r2_hidden(sK3(X0,X1,X1),X0)) )),
% 2.19/0.73    inference(duplicate_literal_removal,[],[f104])).
% 2.19/0.73  fof(f104,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X1 | ~r2_hidden(sK3(X0,X1,X1),X1) | ~r2_hidden(sK3(X0,X1,X1),X0) | k3_xboole_0(X0,X1) = X1) )),
% 2.19/0.73    inference(resolution,[],[f93,f37])).
% 2.19/0.73  fof(f37,plain,(
% 2.19/0.73    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 2.19/0.73    inference(cnf_transformation,[],[f27])).
% 2.19/0.73  fof(f93,plain,(
% 2.19/0.73    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | k3_xboole_0(X0,X1) = X1) )),
% 2.19/0.73    inference(factoring,[],[f36])).
% 2.19/0.73  fof(f187,plain,(
% 2.19/0.73    ( ! [X6,X7] : (k3_xboole_0(X7,X6) = k3_xboole_0(X6,k3_xboole_0(X7,X6)) | r2_hidden(sK3(X6,k3_xboole_0(X7,X6),k3_xboole_0(X7,X6)),X6)) )),
% 2.19/0.73    inference(duplicate_literal_removal,[],[f185])).
% 2.19/0.73  fof(f185,plain,(
% 2.19/0.73    ( ! [X6,X7] : (k3_xboole_0(X7,X6) = k3_xboole_0(X6,k3_xboole_0(X7,X6)) | k3_xboole_0(X7,X6) = k3_xboole_0(X6,k3_xboole_0(X7,X6)) | r2_hidden(sK3(X6,k3_xboole_0(X7,X6),k3_xboole_0(X7,X6)),X6)) )),
% 2.19/0.73    inference(resolution,[],[f108,f89])).
% 2.19/0.73  fof(f89,plain,(
% 2.19/0.73    ( ! [X6,X4,X7,X5] : (r2_hidden(sK3(X4,X5,k3_xboole_0(X6,X7)),X7) | k3_xboole_0(X6,X7) = k3_xboole_0(X4,X5) | r2_hidden(sK3(X4,X5,k3_xboole_0(X6,X7)),X4)) )),
% 2.19/0.73    inference(resolution,[],[f35,f47])).
% 2.19/0.73  fof(f47,plain,(
% 2.19/0.73    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 2.19/0.73    inference(equality_resolution,[],[f33])).
% 2.19/0.73  fof(f33,plain,(
% 2.19/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.19/0.73    inference(cnf_transformation,[],[f27])).
% 2.19/0.73  fof(f35,plain,(
% 2.19/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 2.19/0.73    inference(cnf_transformation,[],[f27])).
% 2.19/0.73  fof(f261,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 2.19/0.73    inference(superposition,[],[f135,f203])).
% 2.19/0.73  fof(f203,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 2.19/0.73    inference(subsumption_resolution,[],[f202,f103])).
% 2.19/0.73  fof(f103,plain,(
% 2.19/0.73    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,X0),X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.19/0.73    inference(subsumption_resolution,[],[f102,f35])).
% 2.19/0.73  fof(f102,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r2_hidden(sK3(X0,X1,X0),X1) | ~r2_hidden(sK3(X0,X1,X0),X0)) )),
% 2.19/0.73    inference(duplicate_literal_removal,[],[f99])).
% 2.19/0.73  fof(f99,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r2_hidden(sK3(X0,X1,X0),X1) | ~r2_hidden(sK3(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) )),
% 2.19/0.73    inference(resolution,[],[f90,f37])).
% 2.19/0.73  fof(f90,plain,(
% 2.19/0.73    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) )),
% 2.19/0.73    inference(factoring,[],[f35])).
% 2.19/0.73  fof(f202,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) | r2_hidden(sK3(k3_xboole_0(X0,X1),X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.19/0.73    inference(duplicate_literal_removal,[],[f194])).
% 2.19/0.73  fof(f194,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) | r2_hidden(sK3(k3_xboole_0(X0,X1),X0,k3_xboole_0(X0,X1)),X0) | k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 2.19/0.73    inference(resolution,[],[f91,f103])).
% 2.19/0.73  fof(f91,plain,(
% 2.19/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(X0,X1,k3_xboole_0(X2,X3)),X2) | k3_xboole_0(X0,X1) = k3_xboole_0(X2,X3) | r2_hidden(sK3(X0,X1,k3_xboole_0(X2,X3)),X1)) )),
% 2.19/0.73    inference(resolution,[],[f36,f48])).
% 2.19/0.73  fof(f48,plain,(
% 2.19/0.73    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 2.19/0.73    inference(equality_resolution,[],[f32])).
% 2.19/0.73  fof(f32,plain,(
% 2.19/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.19/0.73    inference(cnf_transformation,[],[f27])).
% 2.19/0.73  fof(f135,plain,(
% 2.19/0.73    ( ! [X2,X0,X1] : (k3_xboole_0(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X2,X0),X1)) )),
% 2.19/0.73    inference(forward_demodulation,[],[f134,f71])).
% 2.19/0.73  fof(f71,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 2.19/0.73    inference(forward_demodulation,[],[f70,f42])).
% 2.19/0.73  fof(f42,plain,(
% 2.19/0.73    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.19/0.73    inference(cnf_transformation,[],[f10])).
% 2.19/0.73  fof(f10,axiom,(
% 2.19/0.73    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.19/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.19/0.73  fof(f70,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 2.19/0.73    inference(subsumption_resolution,[],[f67,f41])).
% 2.19/0.73  fof(f41,plain,(
% 2.19/0.73    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.19/0.73    inference(cnf_transformation,[],[f16])).
% 2.19/0.73  fof(f16,plain,(
% 2.19/0.73    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.19/0.73    inference(pure_predicate_removal,[],[f12])).
% 2.19/0.73  fof(f12,axiom,(
% 2.19/0.73    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.19/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.19/0.73  fof(f67,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.19/0.73    inference(superposition,[],[f66,f31])).
% 2.19/0.73  fof(f31,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 2.19/0.73    inference(cnf_transformation,[],[f13])).
% 2.19/0.73  fof(f13,axiom,(
% 2.19/0.73    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.19/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 2.19/0.73  fof(f66,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.19/0.73    inference(subsumption_resolution,[],[f65,f41])).
% 2.19/0.73  fof(f65,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k10_relat_1(X1,X0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 2.19/0.73    inference(superposition,[],[f39,f42])).
% 2.19/0.73  fof(f39,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.19/0.73    inference(cnf_transformation,[],[f19])).
% 2.19/0.73  fof(f19,plain,(
% 2.19/0.73    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.19/0.73    inference(ennf_transformation,[],[f9])).
% 2.19/0.73  fof(f9,axiom,(
% 2.19/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.19/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.19/0.73  fof(f134,plain,(
% 2.19/0.73    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(k6_relat_1(X0),X2),X1) = k3_xboole_0(X2,k3_xboole_0(X0,X1))) )),
% 2.19/0.73    inference(forward_demodulation,[],[f133,f71])).
% 2.19/0.73  fof(f133,plain,(
% 2.19/0.73    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(k6_relat_1(X0),X2),X1) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2)) )),
% 2.19/0.73    inference(subsumption_resolution,[],[f129,f41])).
% 2.19/0.73  fof(f129,plain,(
% 2.19/0.73    ( ! [X2,X0,X1] : (k3_xboole_0(k10_relat_1(k6_relat_1(X0),X2),X1) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.19/0.73    inference(superposition,[],[f128,f61])).
% 2.19/0.73  fof(f61,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 2.19/0.73    inference(subsumption_resolution,[],[f59,f41])).
% 2.19/0.73  fof(f59,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X1),X0) | ~v1_relat_1(k6_relat_1(X1))) )),
% 2.19/0.73    inference(superposition,[],[f40,f31])).
% 2.19/0.73  fof(f40,plain,(
% 2.19/0.73    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 2.19/0.73    inference(cnf_transformation,[],[f20])).
% 2.19/0.73  fof(f20,plain,(
% 2.19/0.73    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.19/0.73    inference(ennf_transformation,[],[f11])).
% 2.19/0.73  fof(f11,axiom,(
% 2.19/0.73    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.19/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.19/0.73  fof(f128,plain,(
% 2.19/0.73    ( ! [X4,X5,X3] : (k10_relat_1(k7_relat_1(X4,X3),X5) = k3_xboole_0(k10_relat_1(X4,X5),X3) | ~v1_relat_1(X4)) )),
% 2.19/0.73    inference(forward_demodulation,[],[f83,f71])).
% 2.19/0.73  fof(f83,plain,(
% 2.19/0.73    ( ! [X4,X5,X3] : (k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X4)) )),
% 2.19/0.73    inference(subsumption_resolution,[],[f80,f41])).
% 2.19/0.73  fof(f80,plain,(
% 2.19/0.73    ( ! [X4,X5,X3] : (k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3))) )),
% 2.19/0.73    inference(duplicate_literal_removal,[],[f77])).
% 2.19/0.73  fof(f77,plain,(
% 2.19/0.73    ( ! [X4,X5,X3] : (k10_relat_1(k6_relat_1(X3),k10_relat_1(X4,X5)) = k10_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(X4)) )),
% 2.19/0.73    inference(superposition,[],[f30,f40])).
% 2.19/0.73  fof(f30,plain,(
% 2.19/0.73    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 2.19/0.73    inference(cnf_transformation,[],[f18])).
% 2.19/0.74  fof(f18,plain,(
% 2.19/0.74    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.19/0.74    inference(ennf_transformation,[],[f8])).
% 2.19/0.74  fof(f8,axiom,(
% 2.19/0.74    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 2.19/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).
% 2.19/0.74  fof(f140,plain,(
% 2.19/0.74    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0) | spl4_3),
% 2.19/0.74    inference(avatar_component_clause,[],[f138])).
% 2.19/0.74  fof(f138,plain,(
% 2.19/0.74    spl4_3 <=> k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) = k3_xboole_0(k10_relat_1(sK2,sK1),sK0)),
% 2.19/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.19/0.74  fof(f141,plain,(
% 2.19/0.74    ~spl4_3 | spl4_1 | ~spl4_2),
% 2.19/0.74    inference(avatar_split_clause,[],[f136,f55,f50,f138])).
% 2.19/0.74  fof(f50,plain,(
% 2.19/0.74    spl4_1 <=> k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),
% 2.19/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.19/0.74  fof(f55,plain,(
% 2.19/0.74    spl4_2 <=> v1_relat_1(sK2)),
% 2.19/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.19/0.74  fof(f136,plain,(
% 2.19/0.74    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0) | (spl4_1 | ~spl4_2)),
% 2.19/0.74    inference(subsumption_resolution,[],[f131,f57])).
% 2.19/0.74  fof(f57,plain,(
% 2.19/0.74    v1_relat_1(sK2) | ~spl4_2),
% 2.19/0.74    inference(avatar_component_clause,[],[f55])).
% 2.19/0.74  fof(f131,plain,(
% 2.19/0.74    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k3_xboole_0(k10_relat_1(sK2,sK1),sK0) | ~v1_relat_1(sK2) | spl4_1),
% 2.19/0.74    inference(superposition,[],[f52,f128])).
% 2.19/0.74  fof(f52,plain,(
% 2.19/0.74    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) | spl4_1),
% 2.19/0.74    inference(avatar_component_clause,[],[f50])).
% 2.19/0.74  fof(f58,plain,(
% 2.19/0.74    spl4_2),
% 2.19/0.74    inference(avatar_split_clause,[],[f28,f55])).
% 2.19/0.74  fof(f28,plain,(
% 2.19/0.74    v1_relat_1(sK2)),
% 2.19/0.74    inference(cnf_transformation,[],[f22])).
% 2.19/0.74  fof(f22,plain,(
% 2.19/0.74    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 2.19/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21])).
% 2.19/0.74  fof(f21,plain,(
% 2.19/0.74    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2)) => (k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 2.19/0.74    introduced(choice_axiom,[])).
% 2.19/0.74  fof(f17,plain,(
% 2.19/0.74    ? [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) != k3_xboole_0(X0,k10_relat_1(X2,X1)) & v1_relat_1(X2))),
% 2.19/0.74    inference(ennf_transformation,[],[f15])).
% 2.19/0.74  fof(f15,negated_conjecture,(
% 2.19/0.74    ~! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.19/0.74    inference(negated_conjecture,[],[f14])).
% 2.19/0.74  fof(f14,conjecture,(
% 2.19/0.74    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.19/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 2.19/0.74  fof(f53,plain,(
% 2.19/0.74    ~spl4_1),
% 2.19/0.74    inference(avatar_split_clause,[],[f29,f50])).
% 2.19/0.74  fof(f29,plain,(
% 2.19/0.74    k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),
% 2.19/0.74    inference(cnf_transformation,[],[f22])).
% 2.19/0.74  % SZS output end Proof for theBenchmark
% 2.19/0.74  % (31147)------------------------------
% 2.19/0.74  % (31147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.74  % (31147)Termination reason: Refutation
% 2.19/0.74  
% 2.19/0.74  % (31147)Memory used [KB]: 6524
% 2.19/0.74  % (31147)Time elapsed: 0.149 s
% 2.19/0.74  % (31147)------------------------------
% 2.19/0.74  % (31147)------------------------------
% 2.19/0.74  % (31091)Success in time 0.363 s
%------------------------------------------------------------------------------
