%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:41 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 400 expanded)
%              Number of leaves         :   27 ( 156 expanded)
%              Depth                    :   14
%              Number of atoms          :  478 (1384 expanded)
%              Number of equality atoms :  120 ( 523 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1661,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f90,f197,f348,f607,f1078,f1343,f1568,f1660])).

fof(f1660,plain,
    ( ~ spl4_6
    | spl4_51 ),
    inference(avatar_contradiction_clause,[],[f1655])).

fof(f1655,plain,
    ( $false
    | ~ spl4_6
    | spl4_51 ),
    inference(unit_resulting_resolution,[],[f89,f1567,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(f1567,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | spl4_51 ),
    inference(avatar_component_clause,[],[f1565])).

fof(f1565,plain,
    ( spl4_51
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f89,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1568,plain,
    ( ~ spl4_4
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_5
    | spl4_1
    | ~ spl4_51
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f1563,f1200,f87,f77,f67,f1565,f62,f82,f87,f72,f77])).

fof(f72,plain,
    ( spl4_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f82,plain,
    ( spl4_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f62,plain,
    ( spl4_1
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f67,plain,
    ( spl4_2
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f77,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1200,plain,
    ( spl4_36
  <=> k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f1563,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(duplicate_literal_removal,[],[f1562])).

fof(f1562,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f1561,f69])).

fof(f69,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f1561,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f1560,f381])).

fof(f381,plain,
    ( ! [X1] : k7_relat_1(sK0,X1) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X1)))
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f374,f137])).

fof(f137,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK0)))
    | ~ spl4_6 ),
    inference(superposition,[],[f119,f59])).

fof(f59,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f49,f58,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f119,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X0))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f89,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f374,plain,
    ( ! [X1] : k7_relat_1(sK0,X1) = k7_relat_1(sK0,k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK0))))
    | ~ spl4_6 ),
    inference(superposition,[],[f155,f124])).

fof(f124,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f120,f43])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f120,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(unit_resulting_resolution,[],[f41,f60])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f155,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f148,f43])).

fof(f148,plain,
    ( ! [X0] : k7_relat_1(sK0,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f89,f41,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(f1560,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f1559,f416])).

fof(f416,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f157,f366])).

fof(f366,plain,
    ( ! [X6] : k1_relat_1(k7_relat_1(sK0,X6)) = k1_relat_1(k7_relat_1(k6_relat_1(X6),k1_relat_1(sK0)))
    | ~ spl4_6 ),
    inference(superposition,[],[f124,f137])).

fof(f157,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f156,f43])).

fof(f156,plain,
    ( ! [X0] : k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f147,f69])).

fof(f147,plain,
    ( ! [X0] : k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f79,f41,f45])).

fof(f79,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f1559,plain,
    ( k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_36 ),
    inference(trivial_inequality_removal,[],[f1558])).

fof(f1558,plain,
    ( k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))
    | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_36 ),
    inference(superposition,[],[f48,f1202])).

fof(f1202,plain,
    ( k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f1200])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
                    & r2_hidden(sK3(X0,X1,X2),X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X4] :
                      ( k1_funct_1(X0,X4) = k1_funct_1(X1,X4)
                      | ~ r2_hidden(X4,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                  | ? [X3] :
                      ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
                      & r2_hidden(X3,X2) ) )
                & ( ! [X3] :
                      ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                      | ~ r2_hidden(X3,X2) )
                  | k7_relat_1(X0,X2) != k7_relat_1(X1,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) ) )
              | ~ r1_tarski(X2,k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(X0)) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).

fof(f1343,plain,
    ( spl4_36
    | spl4_1
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f1334,f1076,f62,f1200])).

fof(f1076,plain,
    ( spl4_33
  <=> ! [X3] :
        ( k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1334,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))
    | ~ spl4_33 ),
    inference(resolution,[],[f1077,f39])).

fof(f39,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & ! [X3] :
        ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK2) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(sK0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(X1) = k1_relat_1(sK0) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & ! [X3] :
              ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(sK0) = k1_relat_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & ! [X3] :
            ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
            | ~ r2_hidden(X3,X2) )
        & k1_relat_1(sK0) = k1_relat_1(sK1) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & ! [X3] :
          ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
          | ~ r2_hidden(X3,sK2) )
      & k1_relat_1(sK0) = k1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                  & k1_relat_1(X1) = k1_relat_1(X0) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X0,X3) = k1_funct_1(X1,X3) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).

fof(f1077,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3)
        | k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f1076])).

fof(f1078,plain,
    ( ~ spl4_6
    | spl4_33
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f1061,f605,f1076,f87])).

fof(f605,plain,
    ( spl4_26
  <=> ! [X0] :
        ( k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f1061,plain,
    ( ! [X3] :
        ( k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3)
        | ~ v1_relat_1(sK0) )
    | ~ spl4_26 ),
    inference(resolution,[],[f606,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f606,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
        | k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f605])).

fof(f607,plain,
    ( ~ spl4_6
    | spl4_26
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f603,f346,f87,f77,f67,f605,f87])).

fof(f346,plain,
    ( spl4_22
  <=> ! [X1] :
        ( k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)
        | r2_hidden(sK3(sK1,sK0,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f603,plain,
    ( ! [X0] :
        ( k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
        | ~ v1_relat_1(sK0) )
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f602,f381])).

fof(f602,plain,
    ( ! [X0] :
        ( k7_relat_1(sK1,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
        | ~ v1_relat_1(sK0) )
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f596,f416])).

fof(f596,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
        | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))
        | ~ v1_relat_1(sK0) )
    | ~ spl4_22 ),
    inference(resolution,[],[f347,f52])).

fof(f347,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK1,sK0,X1),X1)
        | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f346])).

fof(f348,plain,
    ( ~ spl4_6
    | spl4_22
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f344,f195,f82,f346,f87])).

fof(f195,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | r2_hidden(sK3(sK1,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f344,plain,
    ( ! [X1] :
        ( k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK1,sK0,X1),X1) )
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,
    ( ! [X1] :
        ( k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK1,sK0,X1),X1) )
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(resolution,[],[f196,f84])).

fof(f84,plain,
    ( v1_funct_1(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | r2_hidden(sK3(sK1,X0,X1),X1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( ~ spl4_4
    | spl4_14
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f193,f72,f67,f195,f77])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK1,X0,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f190,f69])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK1,X0,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | ~ r1_tarski(X1,k1_relat_1(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f47,f74])).

fof(f74,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f34,f87])).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f35,f82])).

fof(f35,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f40,f62])).

fof(f40,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:23:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (3838)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (3829)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (3830)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (3841)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (3845)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (3833)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (3836)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (3842)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (3834)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (3831)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (3835)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (3846)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (3843)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (3844)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (3840)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (3837)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (3839)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.52  % (3832)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.68/0.58  % (3835)Refutation found. Thanks to Tanya!
% 1.68/0.58  % SZS status Theorem for theBenchmark
% 1.68/0.58  % SZS output start Proof for theBenchmark
% 1.68/0.58  fof(f1661,plain,(
% 1.68/0.58    $false),
% 1.68/0.58    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f90,f197,f348,f607,f1078,f1343,f1568,f1660])).
% 1.68/0.58  fof(f1660,plain,(
% 1.68/0.58    ~spl4_6 | spl4_51),
% 1.68/0.58    inference(avatar_contradiction_clause,[],[f1655])).
% 1.68/0.58  fof(f1655,plain,(
% 1.68/0.58    $false | (~spl4_6 | spl4_51)),
% 1.68/0.58    inference(unit_resulting_resolution,[],[f89,f1567,f52])).
% 1.68/0.58  fof(f52,plain,(
% 1.68/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f19])).
% 1.68/0.58  fof(f19,plain,(
% 1.68/0.58    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.68/0.58    inference(ennf_transformation,[],[f7])).
% 1.68/0.58  fof(f7,axiom,(
% 1.68/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
% 1.68/0.58  fof(f1567,plain,(
% 1.68/0.58    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | spl4_51),
% 1.68/0.58    inference(avatar_component_clause,[],[f1565])).
% 1.68/0.58  fof(f1565,plain,(
% 1.68/0.58    spl4_51 <=> r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.68/0.58  fof(f89,plain,(
% 1.68/0.58    v1_relat_1(sK0) | ~spl4_6),
% 1.68/0.58    inference(avatar_component_clause,[],[f87])).
% 1.68/0.58  fof(f87,plain,(
% 1.68/0.58    spl4_6 <=> v1_relat_1(sK0)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.68/0.58  fof(f1568,plain,(
% 1.68/0.58    ~spl4_4 | ~spl4_3 | ~spl4_6 | ~spl4_5 | spl4_1 | ~spl4_51 | ~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_36),
% 1.68/0.58    inference(avatar_split_clause,[],[f1563,f1200,f87,f77,f67,f1565,f62,f82,f87,f72,f77])).
% 1.68/0.58  fof(f72,plain,(
% 1.68/0.58    spl4_3 <=> v1_funct_1(sK1)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.68/0.58  fof(f82,plain,(
% 1.68/0.58    spl4_5 <=> v1_funct_1(sK0)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.68/0.58  fof(f62,plain,(
% 1.68/0.58    spl4_1 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.68/0.58  fof(f67,plain,(
% 1.68/0.58    spl4_2 <=> k1_relat_1(sK0) = k1_relat_1(sK1)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.68/0.58  fof(f77,plain,(
% 1.68/0.58    spl4_4 <=> v1_relat_1(sK1)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.68/0.58  fof(f1200,plain,(
% 1.68/0.58    spl4_36 <=> k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.68/0.58  fof(f1563,plain,(
% 1.68/0.58    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_36)),
% 1.68/0.58    inference(duplicate_literal_removal,[],[f1562])).
% 1.68/0.58  fof(f1562,plain,(
% 1.68/0.58    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_36)),
% 1.68/0.58    inference(forward_demodulation,[],[f1561,f69])).
% 1.68/0.58  fof(f69,plain,(
% 1.68/0.58    k1_relat_1(sK0) = k1_relat_1(sK1) | ~spl4_2),
% 1.68/0.58    inference(avatar_component_clause,[],[f67])).
% 1.68/0.58  fof(f1561,plain,(
% 1.68/0.58    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_36)),
% 1.68/0.58    inference(forward_demodulation,[],[f1560,f381])).
% 1.68/0.58  fof(f381,plain,(
% 1.68/0.58    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X1)))) ) | ~spl4_6),
% 1.68/0.58    inference(forward_demodulation,[],[f374,f137])).
% 1.68/0.58  fof(f137,plain,(
% 1.68/0.58    ( ! [X1] : (k1_relat_1(k7_relat_1(sK0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK0)))) ) | ~spl4_6),
% 1.68/0.58    inference(superposition,[],[f119,f59])).
% 1.68/0.58  fof(f59,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 1.68/0.58    inference(definition_unfolding,[],[f49,f58,f58])).
% 1.68/0.58  fof(f58,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.68/0.58    inference(definition_unfolding,[],[f50,f51])).
% 1.68/0.58  fof(f51,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f2])).
% 1.68/0.58  fof(f2,axiom,(
% 1.68/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.68/0.58  fof(f50,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f3])).
% 1.68/0.58  fof(f3,axiom,(
% 1.68/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.68/0.58  fof(f49,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f1])).
% 1.68/0.58  fof(f1,axiom,(
% 1.68/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.68/0.58  fof(f119,plain,(
% 1.68/0.58    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X0))) ) | ~spl4_6),
% 1.68/0.58    inference(unit_resulting_resolution,[],[f89,f60])).
% 1.68/0.58  fof(f60,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 1.68/0.58    inference(definition_unfolding,[],[f53,f58])).
% 1.68/0.58  fof(f53,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f20])).
% 1.68/0.58  fof(f20,plain,(
% 1.68/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.68/0.58    inference(ennf_transformation,[],[f8])).
% 1.68/0.58  fof(f8,axiom,(
% 1.68/0.58    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.68/0.58  fof(f374,plain,(
% 1.68/0.58    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK0,k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK0))))) ) | ~spl4_6),
% 1.68/0.58    inference(superposition,[],[f155,f124])).
% 1.68/0.58  fof(f124,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.68/0.58    inference(forward_demodulation,[],[f120,f43])).
% 1.68/0.58  fof(f43,plain,(
% 1.68/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.68/0.58    inference(cnf_transformation,[],[f5])).
% 1.68/0.58  fof(f5,axiom,(
% 1.68/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.68/0.58  fof(f120,plain,(
% 1.68/0.58    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) )),
% 1.68/0.58    inference(unit_resulting_resolution,[],[f41,f60])).
% 1.68/0.58  fof(f41,plain,(
% 1.68/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f10])).
% 1.68/0.58  fof(f10,axiom,(
% 1.68/0.58    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.68/0.58  fof(f155,plain,(
% 1.68/0.58    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))) ) | ~spl4_6),
% 1.68/0.58    inference(forward_demodulation,[],[f148,f43])).
% 1.68/0.58  fof(f148,plain,(
% 1.68/0.58    ( ! [X0] : (k7_relat_1(sK0,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))) ) | ~spl4_6),
% 1.68/0.58    inference(unit_resulting_resolution,[],[f89,f41,f45])).
% 1.68/0.58  fof(f45,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  fof(f16,plain,(
% 1.68/0.58    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.68/0.58    inference(ennf_transformation,[],[f4])).
% 1.68/0.58  fof(f4,axiom,(
% 1.68/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).
% 1.68/0.58  fof(f1560,plain,(
% 1.68/0.58    k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_36)),
% 1.68/0.58    inference(forward_demodulation,[],[f1559,f416])).
% 1.68/0.58  fof(f416,plain,(
% 1.68/0.58    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))) ) | (~spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.68/0.58    inference(backward_demodulation,[],[f157,f366])).
% 1.68/0.58  fof(f366,plain,(
% 1.68/0.58    ( ! [X6] : (k1_relat_1(k7_relat_1(sK0,X6)) = k1_relat_1(k7_relat_1(k6_relat_1(X6),k1_relat_1(sK0)))) ) | ~spl4_6),
% 1.68/0.58    inference(superposition,[],[f124,f137])).
% 1.68/0.58  fof(f157,plain,(
% 1.68/0.58    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))) ) | (~spl4_2 | ~spl4_4)),
% 1.68/0.58    inference(forward_demodulation,[],[f156,f43])).
% 1.68/0.58  fof(f156,plain,(
% 1.68/0.58    ( ! [X0] : (k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK0))))) ) | (~spl4_2 | ~spl4_4)),
% 1.68/0.58    inference(forward_demodulation,[],[f147,f69])).
% 1.68/0.58  fof(f147,plain,(
% 1.68/0.58    ( ! [X0] : (k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))))) ) | ~spl4_4),
% 1.68/0.58    inference(unit_resulting_resolution,[],[f79,f41,f45])).
% 1.68/0.58  fof(f79,plain,(
% 1.68/0.58    v1_relat_1(sK1) | ~spl4_4),
% 1.68/0.58    inference(avatar_component_clause,[],[f77])).
% 1.68/0.58  fof(f1559,plain,(
% 1.68/0.58    k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_36),
% 1.68/0.58    inference(trivial_inequality_removal,[],[f1558])).
% 1.68/0.58  fof(f1558,plain,(
% 1.68/0.58    k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_36),
% 1.68/0.58    inference(superposition,[],[f48,f1202])).
% 1.68/0.58  fof(f1202,plain,(
% 1.68/0.58    k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) | ~spl4_36),
% 1.68/0.58    inference(avatar_component_clause,[],[f1200])).
% 1.68/0.58  fof(f48,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f31])).
% 1.68/0.58  fof(f31,plain,(
% 1.68/0.58    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.68/0.58  fof(f30,plain,(
% 1.68/0.58    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2)))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f29,plain,(
% 1.68/0.58    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.58    inference(rectify,[],[f28])).
% 1.68/0.58  fof(f28,plain,(
% 1.68/0.58    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.58    inference(nnf_transformation,[],[f18])).
% 1.68/0.58  fof(f18,plain,(
% 1.68/0.58    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.68/0.58    inference(flattening,[],[f17])).
% 1.68/0.58  fof(f17,plain,(
% 1.68/0.58    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.68/0.58    inference(ennf_transformation,[],[f11])).
% 1.68/0.58  fof(f11,axiom,(
% 1.68/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).
% 1.68/0.58  fof(f1343,plain,(
% 1.68/0.58    spl4_36 | spl4_1 | ~spl4_33),
% 1.68/0.58    inference(avatar_split_clause,[],[f1334,f1076,f62,f1200])).
% 1.68/0.58  fof(f1076,plain,(
% 1.68/0.58    spl4_33 <=> ! [X3] : (k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.68/0.58  fof(f1334,plain,(
% 1.68/0.58    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) | ~spl4_33),
% 1.68/0.58    inference(resolution,[],[f1077,f39])).
% 1.68/0.58  fof(f39,plain,(
% 1.68/0.58    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  fof(f27,plain,(
% 1.68/0.58    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.68/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f26,f25,f24])).
% 1.68/0.58  fof(f24,plain,(
% 1.68/0.58    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f25,plain,(
% 1.68/0.58    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f26,plain,(
% 1.68/0.58    ? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f15,plain,(
% 1.68/0.58    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.68/0.58    inference(flattening,[],[f14])).
% 1.68/0.58  fof(f14,plain,(
% 1.68/0.58    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.68/0.58    inference(ennf_transformation,[],[f13])).
% 1.68/0.58  fof(f13,negated_conjecture,(
% 1.68/0.58    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 1.68/0.58    inference(negated_conjecture,[],[f12])).
% 1.68/0.58  fof(f12,conjecture,(
% 1.68/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).
% 1.68/0.58  fof(f1077,plain,(
% 1.68/0.58    ( ! [X3] : (r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3) | k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)) ) | ~spl4_33),
% 1.68/0.58    inference(avatar_component_clause,[],[f1076])).
% 1.68/0.58  fof(f1078,plain,(
% 1.68/0.58    ~spl4_6 | spl4_33 | ~spl4_26),
% 1.68/0.58    inference(avatar_split_clause,[],[f1061,f605,f1076,f87])).
% 1.68/0.58  fof(f605,plain,(
% 1.68/0.58    spl4_26 <=> ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.68/0.58  fof(f1061,plain,(
% 1.68/0.58    ( ! [X3] : (k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3) | ~v1_relat_1(sK0)) ) | ~spl4_26),
% 1.68/0.58    inference(resolution,[],[f606,f55])).
% 1.68/0.58  fof(f55,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f33])).
% 1.68/0.58  fof(f33,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.68/0.58    inference(flattening,[],[f32])).
% 1.68/0.58  fof(f32,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.68/0.58    inference(nnf_transformation,[],[f23])).
% 1.68/0.58  fof(f23,plain,(
% 1.68/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 1.68/0.58    inference(ennf_transformation,[],[f6])).
% 1.68/0.58  fof(f6,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 1.68/0.58  fof(f606,plain,(
% 1.68/0.58    ( ! [X0] : (r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0)) ) | ~spl4_26),
% 1.68/0.58    inference(avatar_component_clause,[],[f605])).
% 1.68/0.58  fof(f607,plain,(
% 1.68/0.58    ~spl4_6 | spl4_26 | ~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_22),
% 1.68/0.58    inference(avatar_split_clause,[],[f603,f346,f87,f77,f67,f605,f87])).
% 1.68/0.58  fof(f346,plain,(
% 1.68/0.58    spl4_22 <=> ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) | r2_hidden(sK3(sK1,sK0,X1),X1) | ~r1_tarski(X1,k1_relat_1(sK0)))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.68/0.58  fof(f603,plain,(
% 1.68/0.58    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) ) | (~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_22)),
% 1.68/0.58    inference(forward_demodulation,[],[f602,f381])).
% 1.68/0.58  fof(f602,plain,(
% 1.68/0.58    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) ) | (~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_22)),
% 1.68/0.58    inference(forward_demodulation,[],[f596,f416])).
% 1.68/0.58  fof(f596,plain,(
% 1.68/0.58    ( ! [X0] : (r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) ) | ~spl4_22),
% 1.68/0.58    inference(resolution,[],[f347,f52])).
% 1.68/0.58  fof(f347,plain,(
% 1.68/0.58    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,sK0,X1),X1) | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)) ) | ~spl4_22),
% 1.68/0.58    inference(avatar_component_clause,[],[f346])).
% 1.68/0.58  fof(f348,plain,(
% 1.68/0.58    ~spl4_6 | spl4_22 | ~spl4_5 | ~spl4_14),
% 1.68/0.58    inference(avatar_split_clause,[],[f344,f195,f82,f346,f87])).
% 1.68/0.58  fof(f195,plain,(
% 1.68/0.58    spl4_14 <=> ! [X1,X0] : (~r1_tarski(X1,k1_relat_1(sK0)) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | r2_hidden(sK3(sK1,X0,X1),X1))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.68/0.58  fof(f344,plain,(
% 1.68/0.58    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK0) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,sK0,X1),X1)) ) | (~spl4_5 | ~spl4_14)),
% 1.68/0.58    inference(duplicate_literal_removal,[],[f342])).
% 1.68/0.58  fof(f342,plain,(
% 1.68/0.58    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK0) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,sK0,X1),X1)) ) | (~spl4_5 | ~spl4_14)),
% 1.68/0.58    inference(resolution,[],[f196,f84])).
% 1.68/0.58  fof(f84,plain,(
% 1.68/0.58    v1_funct_1(sK0) | ~spl4_5),
% 1.68/0.58    inference(avatar_component_clause,[],[f82])).
% 1.68/0.58  fof(f196,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~v1_funct_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(X0) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~r1_tarski(X1,k1_relat_1(X0)) | r2_hidden(sK3(sK1,X0,X1),X1)) ) | ~spl4_14),
% 1.68/0.58    inference(avatar_component_clause,[],[f195])).
% 1.68/0.58  fof(f197,plain,(
% 1.68/0.58    ~spl4_4 | spl4_14 | ~spl4_2 | ~spl4_3),
% 1.68/0.58    inference(avatar_split_clause,[],[f193,f72,f67,f195,f77])).
% 1.68/0.58  fof(f193,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,X0,X1),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK1)) ) | (~spl4_2 | ~spl4_3)),
% 1.68/0.58    inference(forward_demodulation,[],[f190,f69])).
% 1.68/0.58  fof(f190,plain,(
% 1.68/0.58    ( ! [X0,X1] : (r2_hidden(sK3(sK1,X0,X1),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | ~r1_tarski(X1,k1_relat_1(sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK1)) ) | ~spl4_3),
% 1.68/0.58    inference(resolution,[],[f47,f74])).
% 1.68/0.58  fof(f74,plain,(
% 1.68/0.58    v1_funct_1(sK1) | ~spl4_3),
% 1.68/0.58    inference(avatar_component_clause,[],[f72])).
% 1.68/0.58  fof(f47,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK3(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~v1_relat_1(X0)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f31])).
% 1.68/0.58  fof(f90,plain,(
% 1.68/0.58    spl4_6),
% 1.68/0.58    inference(avatar_split_clause,[],[f34,f87])).
% 1.68/0.58  fof(f34,plain,(
% 1.68/0.58    v1_relat_1(sK0)),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  fof(f85,plain,(
% 1.68/0.58    spl4_5),
% 1.68/0.58    inference(avatar_split_clause,[],[f35,f82])).
% 1.68/0.58  fof(f35,plain,(
% 1.68/0.58    v1_funct_1(sK0)),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  fof(f80,plain,(
% 1.68/0.58    spl4_4),
% 1.68/0.58    inference(avatar_split_clause,[],[f36,f77])).
% 1.68/0.58  fof(f36,plain,(
% 1.68/0.58    v1_relat_1(sK1)),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  fof(f75,plain,(
% 1.68/0.58    spl4_3),
% 1.68/0.58    inference(avatar_split_clause,[],[f37,f72])).
% 1.68/0.58  fof(f37,plain,(
% 1.68/0.58    v1_funct_1(sK1)),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  fof(f70,plain,(
% 1.68/0.58    spl4_2),
% 1.68/0.58    inference(avatar_split_clause,[],[f38,f67])).
% 1.68/0.58  fof(f38,plain,(
% 1.68/0.58    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  fof(f65,plain,(
% 1.68/0.58    ~spl4_1),
% 1.68/0.58    inference(avatar_split_clause,[],[f40,f62])).
% 1.68/0.58  fof(f40,plain,(
% 1.68/0.58    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  % SZS output end Proof for theBenchmark
% 1.68/0.58  % (3835)------------------------------
% 1.68/0.58  % (3835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (3835)Termination reason: Refutation
% 1.68/0.58  
% 1.68/0.58  % (3835)Memory used [KB]: 7164
% 1.68/0.58  % (3835)Time elapsed: 0.110 s
% 1.68/0.58  % (3835)------------------------------
% 1.68/0.58  % (3835)------------------------------
% 1.68/0.58  % (3828)Success in time 0.223 s
%------------------------------------------------------------------------------
