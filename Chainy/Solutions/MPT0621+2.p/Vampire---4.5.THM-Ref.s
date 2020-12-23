%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0621+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:40 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 261 expanded)
%              Number of leaves         :    8 (  78 expanded)
%              Depth                    :   20
%              Number of atoms          :  171 (1427 expanded)
%              Number of equality atoms :  114 ( 820 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1977,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1798,f1976])).

fof(f1976,plain,(
    ! [X128,X126] : X126 = X128 ),
    inference(subsumption_resolution,[],[f1789,f1753])).

fof(f1753,plain,(
    ! [X4,X5,X3] : k2_tarski(X5,X3) = k2_xboole_0(k2_tarski(X5,X5),k2_relat_1(sK7(sK4,X4))) ),
    inference(superposition,[],[f1563,f1711])).

fof(f1711,plain,(
    ! [X6,X7] : k2_tarski(X6,X6) = k2_relat_1(sK7(sK4,X7)) ),
    inference(subsumption_resolution,[],[f1706,f1231])).

fof(f1231,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f1109])).

fof(f1109,plain,
    ( k1_xboole_0 != sK4
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK4
            | k1_relat_1(X1) != sK4
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f911,f1108])).

fof(f1108,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK4
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK4
              | k1_relat_1(X1) != sK4
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f911,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f910])).

fof(f910,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f903])).

fof(f903,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f902])).

fof(f902,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f1706,plain,(
    ! [X6,X7] :
      ( k2_tarski(X6,X6) = k2_relat_1(sK7(sK4,X7))
      | k1_xboole_0 = sK4 ) ),
    inference(superposition,[],[f1564,f1698])).

fof(f1698,plain,(
    ! [X0,X1] : sK7(sK4,X0) = sK7(sK4,X1) ),
    inference(subsumption_resolution,[],[f1697,f1231])).

fof(f1697,plain,(
    ! [X0,X1] :
      ( sK7(sK4,X0) = sK7(sK4,X1)
      | k1_xboole_0 = sK4 ) ),
    inference(equality_resolution,[],[f1696])).

fof(f1696,plain,(
    ! [X2,X0,X1] :
      ( sK4 != X0
      | sK7(X0,X1) = sK7(sK4,X2)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1695,f1231])).

fof(f1695,plain,(
    ! [X2,X0,X1] :
      ( sK7(X0,X1) = sK7(sK4,X2)
      | sK4 != X0
      | k1_xboole_0 = sK4
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f1694])).

fof(f1694,plain,(
    ! [X2,X0,X3,X1] :
      ( sK4 != X2
      | sK7(X0,X1) = sK7(X2,X3)
      | sK4 != X0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1693,f1242])).

fof(f1242,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK7(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1115])).

fof(f1115,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK7(X0,X1))
          & k1_relat_1(sK7(X0,X1)) = X0
          & v1_funct_1(sK7(X0,X1))
          & v1_relat_1(sK7(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f919,f1114])).

fof(f1114,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK7(X0,X1))
        & k1_relat_1(sK7(X0,X1)) = X0
        & v1_funct_1(sK7(X0,X1))
        & v1_relat_1(sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f919,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f901])).

fof(f901,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f1693,plain,(
    ! [X2,X0,X3,X1] :
      ( sK4 != X0
      | sK7(X0,X1) = sK7(X2,X3)
      | sK4 != X2
      | ~ v1_relat_1(sK7(X0,X1))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1689,f1243])).

fof(f1243,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK7(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1115])).

fof(f1689,plain,(
    ! [X2,X0,X3,X1] :
      ( sK4 != X0
      | sK7(X0,X1) = sK7(X2,X3)
      | sK4 != X2
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f1688,f1244])).

fof(f1244,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK7(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1115])).

fof(f1688,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != sK4
      | sK7(X0,X1) = X2
      | sK4 != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1687,f1242])).

fof(f1687,plain,(
    ! [X2,X0,X1] :
      ( sK4 != X0
      | sK7(X0,X1) = X2
      | k1_relat_1(X2) != sK4
      | ~ v1_relat_1(sK7(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1683,f1243])).

fof(f1683,plain,(
    ! [X2,X0,X1] :
      ( sK4 != X0
      | sK7(X0,X1) = X2
      | k1_relat_1(X2) != sK4
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ v1_relat_1(sK7(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f1230,f1244])).

fof(f1230,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK4
      | X1 = X2
      | k1_relat_1(X1) != sK4
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1109])).

fof(f1564,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK7(X0,X1)) = k2_tarski(X1,X1)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f1245,f1562])).

fof(f1562,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f1245,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK7(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1115])).

fof(f1563,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ),
    inference(definition_unfolding,[],[f1556,f1562,f1562])).

fof(f1556,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f1789,plain,(
    ! [X127,X128,X126] :
      ( k2_tarski(X128,X128) != k2_xboole_0(k2_tarski(X128,X128),k2_relat_1(sK7(sK4,X127)))
      | X126 = X128 ) ),
    inference(superposition,[],[f1596,f1711])).

fof(f1596,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k2_tarski(X0,X0) != k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f1364,f1562,f1562,f1562])).

fof(f1364,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f980])).

fof(f980,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f356])).

fof(f356,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f1798,plain,(
    ! [X154,X155] : k1_xboole_0 != k2_xboole_0(k2_relat_1(sK7(sK4,X154)),X155) ),
    inference(superposition,[],[f1603,f1711])).

fof(f1603,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(definition_unfolding,[],[f1371,f1562])).

fof(f1371,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f407])).

fof(f407,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
