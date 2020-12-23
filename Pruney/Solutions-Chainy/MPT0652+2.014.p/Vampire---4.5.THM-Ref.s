%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 219 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  316 ( 908 expanded)
%              Number of equality atoms :   73 ( 298 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f91,f95,f143,f160,f168,f172,f223])).

fof(f223,plain,
    ( spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f221,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f221,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f220,f30])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f220,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f219,f33])).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f219,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(trivial_inequality_removal,[],[f214])).

fof(f214,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | k1_relat_1(sK0) != k2_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(superposition,[],[f210,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f210,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f209,f153])).

fof(f153,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl1_7
  <=> k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f209,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f208,f81])).

fof(f81,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl1_3
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f208,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_2 ),
    inference(subsumption_resolution,[],[f206,f26])).

fof(f206,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl1_2 ),
    inference(superposition,[],[f53,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

fof(f53,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f172,plain,
    ( spl1_7
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f171,f147,f84,f151])).

fof(f84,plain,
    ( spl1_4
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f147,plain,
    ( spl1_6
  <=> r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f171,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ spl1_4
    | ~ spl1_6 ),
    inference(subsumption_resolution,[],[f169,f85])).

fof(f85,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f169,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | ~ spl1_6 ),
    inference(resolution,[],[f148,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f148,plain,
    ( r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f168,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl1_6 ),
    inference(subsumption_resolution,[],[f166,f26])).

fof(f166,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f165,f27])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f165,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f164,f28])).

fof(f28,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f164,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(subsumption_resolution,[],[f163,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f163,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_6 ),
    inference(superposition,[],[f149,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f149,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f160,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl1_5 ),
    inference(subsumption_resolution,[],[f158,f26])).

fof(f158,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(subsumption_resolution,[],[f157,f27])).

fof(f157,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(subsumption_resolution,[],[f156,f28])).

fof(f156,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(trivial_inequality_removal,[],[f155])).

fof(f155,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_5 ),
    inference(superposition,[],[f90,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl1_5
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f143,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl1_4 ),
    inference(subsumption_resolution,[],[f141,f26])).

fof(f141,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(subsumption_resolution,[],[f140,f27])).

fof(f140,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(subsumption_resolution,[],[f139,f28])).

fof(f139,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(subsumption_resolution,[],[f138,f44])).

fof(f138,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(superposition,[],[f86,f40])).

fof(f86,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f95,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f93,f26])).

fof(f93,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f92,f27])).

fof(f92,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f82,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f82,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f91,plain,
    ( ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | spl1_1 ),
    inference(avatar_split_clause,[],[f78,f47,f88,f84,f80])).

fof(f47,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f78,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(subsumption_resolution,[],[f69,f26])).

fof(f69,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(superposition,[],[f49,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f49,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f54,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f29,f51,f47])).

fof(f29,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:33:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (31299)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (31290)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (31310)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (31309)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (31302)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (31290)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (31313)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f54,f91,f95,f143,f160,f168,f172,f223])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    spl1_2 | ~spl1_3 | ~spl1_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f222])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    $false | (spl1_2 | ~spl1_3 | ~spl1_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f221,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3 | ~spl1_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f220,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    ~v1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3 | ~spl1_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f219,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k2_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3 | ~spl1_7)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f214])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    k2_relat_1(sK0) != k2_relat_1(sK0) | k1_relat_1(sK0) != k2_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k1_relat_1(sK0))) | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_3 | ~spl1_7)),
% 0.21/0.51    inference(superposition,[],[f210,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k1_relat_1(sK0) | ~v1_relat_1(X0)) ) | (spl1_2 | ~spl1_3 | ~spl1_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f209,f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) | ~spl1_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f151])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl1_7 <=> k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | (spl1_2 | ~spl1_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f208,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK0)) | ~spl1_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl1_3 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | spl1_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f206,f26])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X0)) ) | spl1_2),
% 0.21/0.51    inference(superposition,[],[f53,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl1_2 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    spl1_7 | ~spl1_4 | ~spl1_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f171,f147,f84,f151])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl1_4 <=> r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl1_6 <=> r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) | (~spl1_4 | ~spl1_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f169,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) | ~spl1_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) | ~spl1_6),
% 0.21/0.51    inference(resolution,[],[f148,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | ~spl1_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f147])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    spl1_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f167])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    $false | spl1_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f166,f26])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | spl1_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f165,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v1_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f164,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    v2_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f163,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_6),
% 0.21/0.51    inference(superposition,[],[f149,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) | spl1_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f147])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl1_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    $false | spl1_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f158,f26])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | spl1_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f157,f27])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f156,f28])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_5),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    k2_relat_1(sK0) != k2_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_5),
% 0.21/0.51    inference(superposition,[],[f90,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | spl1_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl1_5 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl1_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    $false | spl1_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f141,f26])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | spl1_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f140,f27])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f139,f28])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f138,f44])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_4),
% 0.21/0.51    inference(superposition,[],[f86,f40])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) | spl1_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl1_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    $false | spl1_3),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f26])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | spl1_3),
% 0.21/0.51    inference(subsumption_resolution,[],[f92,f27])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_3),
% 0.21/0.51    inference(resolution,[],[f82,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK0)) | spl1_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~spl1_3 | ~spl1_4 | ~spl1_5 | spl1_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f78,f47,f88,f84,f80])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    spl1_1 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | spl1_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f26])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | spl1_1),
% 0.21/0.51    inference(superposition,[],[f49,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f47])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ~spl1_1 | ~spl1_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f51,f47])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (31290)------------------------------
% 0.21/0.51  % (31290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31290)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (31290)Memory used [KB]: 6140
% 0.21/0.51  % (31290)Time elapsed: 0.094 s
% 0.21/0.51  % (31290)------------------------------
% 0.21/0.51  % (31290)------------------------------
% 0.21/0.51  % (31307)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (31278)Success in time 0.152 s
%------------------------------------------------------------------------------
