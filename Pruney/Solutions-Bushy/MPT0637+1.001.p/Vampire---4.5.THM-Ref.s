%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0637+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:21 EST 2020

% Result     : Theorem 31.58s
% Output     : Refutation 31.58s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 345 expanded)
%              Number of leaves         :   21 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          :  464 (1360 expanded)
%              Number of equality atoms :  130 ( 488 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34706,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f646,f877,f987,f16568,f34684,f34691,f34705])).

fof(f34705,plain,
    ( spl5_1
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f34704])).

fof(f34704,plain,
    ( $false
    | spl5_1
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f34703,f70])).

fof(f70,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f69,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f69,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f63,f42])).

fof(f42,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f34703,plain,
    ( k3_xboole_0(sK0,sK1) != k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | spl5_1
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f34702,f86])).

fof(f86,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k3_xboole_0(X1,X0) ),
    inference(forward_demodulation,[],[f83,f70])).

fof(f83,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k3_xboole_0(k1_relat_1(k6_relat_1(X1)),X0) ),
    inference(unit_resulting_resolution,[],[f40,f42,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

fof(f34702,plain,
    ( k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | spl5_1
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f34701,f40])).

fof(f34701,plain,
    ( k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | spl5_1
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f34700,f42])).

fof(f34700,plain,
    ( k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | spl5_1
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f34699,f76])).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f40,f40,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f34699,plain,
    ( k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | spl5_1
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f34698,f82])).

fof(f82,plain,(
    ! [X0,X1] : v1_funct_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f40,f42,f40,f42,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f34698,plain,
    ( k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | spl5_1
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f34697,f74])).

fof(f74,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_1
  <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f34697,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1))
    | k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl5_14
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f34696,f16567])).

fof(f16567,plain,
    ( sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f16565])).

fof(f16565,plain,
    ( spl5_14
  <=> sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f34696,plain,
    ( sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) != k1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))
    | k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1))
    | k1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1))) != k1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(k6_relat_1(k3_xboole_0(sK0,sK1)))
    | ~ spl5_19 ),
    inference(superposition,[],[f44,f34690])).

fof(f34690,plain,
    ( sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f34688])).

fof(f34688,plain,
    ( spl5_19
  <=> sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK2(X0,X1)) != k1_funct_1(X0,sK2(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X1,sK2(X0,X1)) != k1_funct_1(X0,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X1,sK2(X0,X1)) != k1_funct_1(X0,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X1,X2) = k1_funct_1(X0,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f34691,plain,
    ( spl5_19
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f34686,f34681,f984,f874,f34688])).

fof(f874,plain,
    ( spl5_3
  <=> r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f984,plain,
    ( spl5_4
  <=> r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f34681,plain,
    ( spl5_18
  <=> k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = k1_funct_1(k6_relat_1(sK0),k1_funct_1(k6_relat_1(sK1),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f34686,plain,
    ( sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f34685,f1121])).

fof(f1121,plain,
    ( sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) = k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f876,f68])).

fof(f68,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(k6_relat_1(X0),X3) = X3 ) ),
    inference(subsumption_resolution,[],[f67,f40])).

fof(f67,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f62,f42])).

fof(f62,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f876,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f874])).

fof(f34685,plain,
    ( k1_funct_1(k6_relat_1(sK0),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f34683,f1439])).

fof(f1439,plain,
    ( sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) = k1_funct_1(k6_relat_1(sK1),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f986,f68])).

fof(f986,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f984])).

fof(f34683,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = k1_funct_1(k6_relat_1(sK0),k1_funct_1(k6_relat_1(sK1),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f34681])).

fof(f34684,plain,
    ( spl5_18
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1371,f643,f34681])).

fof(f643,plain,
    ( spl5_2
  <=> r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1371,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))) = k1_funct_1(k6_relat_1(sK0),k1_funct_1(k6_relat_1(sK1),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)))))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f645,f327])).

fof(f327,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X2,X1))
      | k1_funct_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) = k1_funct_1(k6_relat_1(X2),k1_funct_1(k6_relat_1(X1),X0)) ) ),
    inference(forward_demodulation,[],[f326,f86])).

fof(f326,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))
      | k1_funct_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) = k1_funct_1(k6_relat_1(X2),k1_funct_1(k6_relat_1(X1),X0)) ) ),
    inference(subsumption_resolution,[],[f323,f40])).

fof(f323,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))
      | ~ v1_relat_1(k6_relat_1(X1))
      | k1_funct_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) = k1_funct_1(k6_relat_1(X2),k1_funct_1(k6_relat_1(X1),X0)) ) ),
    inference(resolution,[],[f150,f42])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,k6_relat_1(X2)),X0) = k1_funct_1(k6_relat_1(X2),k1_funct_1(X1,X0)) ) ),
    inference(subsumption_resolution,[],[f147,f40])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,k6_relat_1(X2)),X0) = k1_funct_1(k6_relat_1(X2),k1_funct_1(X1,X0))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f52,f42])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f645,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),k3_xboole_0(sK0,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f643])).

fof(f16568,plain,
    ( spl5_14
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f651,f643,f16565])).

fof(f651,plain,
    ( sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_xboole_0(sK0,sK1)),sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f645,f68])).

fof(f987,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f648,f643,f984])).

fof(f648,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f645,f65])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f877,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f647,f643,f874])).

fof(f647,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f645,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f646,plain,
    ( spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f172,f72,f643])).

fof(f172,plain,
    ( r2_hidden(sK2(k6_relat_1(k3_xboole_0(sK0,sK1)),k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),k3_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f82,f76,f74,f86,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r2_hidden(sK2(k6_relat_1(X0),X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(forward_demodulation,[],[f117,f70])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k6_relat_1(X0),X1),X0)
      | k1_relat_1(X1) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(forward_demodulation,[],[f116,f70])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0)))
      | k1_relat_1(X1) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f114,f40])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0)))
      | k1_relat_1(X1) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(X0) = X1
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f43,f42])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f39,f72])).

fof(f39,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25])).

fof(f25,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

%------------------------------------------------------------------------------
