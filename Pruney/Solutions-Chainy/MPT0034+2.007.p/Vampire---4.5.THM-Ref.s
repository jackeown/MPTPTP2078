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
% DateTime   : Thu Dec  3 12:29:43 EST 2020

% Result     : Theorem 16.56s
% Output     : Refutation 16.56s
% Verified   : 
% Statistics : Number of formulae       :  214 (1238 expanded)
%              Number of leaves         :   45 ( 359 expanded)
%              Depth                    :   19
%              Number of atoms          :  601 (4064 expanded)
%              Number of equality atoms :   71 ( 350 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12501,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f84,f93,f96,f103,f197,f466,f825,f1198,f1206,f1962,f2070,f2168,f2188,f2196,f3035,f3094,f3149,f3161,f3442,f3860,f5421,f5544,f5549,f5554,f7459,f7542,f12328,f12498])).

fof(f12498,plain,
    ( ~ spl5_2
    | spl5_6
    | ~ spl5_35 ),
    inference(avatar_contradiction_clause,[],[f12497])).

fof(f12497,plain,
    ( $false
    | ~ spl5_2
    | spl5_6
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f12440,f92])).

fof(f92,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_6
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f12440,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),sK3)
    | ~ spl5_2
    | ~ spl5_35 ),
    inference(resolution,[],[f12327,f407])).

fof(f407,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k3_xboole_0(sK2,X1))
        | r1_tarski(X0,sK3) )
    | ~ spl5_2 ),
    inference(condensation,[],[f399])).

fof(f399,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k3_xboole_0(sK2,X1))
        | ~ r1_tarski(X0,X2)
        | r1_tarski(X0,sK3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f337,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k3_xboole_0(X2,X1),X3)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X3) ) ),
    inference(resolution,[],[f32,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f337,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(k3_xboole_0(sK2,X0),X1),sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f233,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f233,plain,
    ( ! [X61,X60] :
        ( ~ r1_tarski(X60,sK2)
        | r1_tarski(k3_xboole_0(X60,X61),sK3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f79,f44])).

fof(f44,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X3),X2) ) ),
    inference(resolution,[],[f53,f31])).

fof(f53,plain,(
    ! [X8,X7,X9] :
      ( r1_tarski(k3_xboole_0(X7,X9),X8)
      | ~ r1_tarski(X7,X8) ) ),
    inference(resolution,[],[f31,f28])).

fof(f12327,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,sK2))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f12325])).

fof(f12325,plain,
    ( spl5_35
  <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f12328,plain,
    ( spl5_35
    | ~ spl5_2
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f12197,f7456,f42,f12325])).

fof(f7456,plain,
    ( spl5_33
  <=> r1_tarski(sK0,k3_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f12197,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,sK2))
    | ~ spl5_2
    | ~ spl5_33 ),
    inference(superposition,[],[f9065,f1943])).

fof(f1943,plain,
    ( ! [X39] : k3_xboole_0(sK2,sK2) = k3_xboole_0(k2_xboole_0(X39,sK3),sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f721,f569])).

fof(f569,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(sK2,X0),k2_xboole_0(X1,sK3))
    | ~ spl5_2 ),
    inference(resolution,[],[f512,f28])).

fof(f512,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(X0,k2_xboole_0(X1,sK3)) )
    | ~ spl5_2 ),
    inference(condensation,[],[f501])).

fof(f501,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(X0,k2_xboole_0(X2,sK3))
        | ~ r1_tarski(X0,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f491,f131])).

fof(f131,plain,(
    ! [X19,X17,X20,X18,X16] :
      ( ~ r1_tarski(k3_xboole_0(X17,X18),X20)
      | ~ r1_tarski(X16,X18)
      | r1_tarski(X16,k2_xboole_0(X19,X20))
      | ~ r1_tarski(X16,X17) ) ),
    inference(resolution,[],[f60,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f491,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f426,f28])).

fof(f426,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(X0,sK3) )
    | ~ spl5_2 ),
    inference(condensation,[],[f414])).

fof(f414,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,sK3)
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f407,f32])).

fof(f721,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,X2),X3)
      | k3_xboole_0(X2,X2) = k3_xboole_0(X3,X2) ) ),
    inference(subsumption_resolution,[],[f719,f28])).

fof(f719,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,X2),X3)
      | k3_xboole_0(X2,X2) = k3_xboole_0(X3,X2)
      | ~ r1_tarski(k3_xboole_0(X2,X2),X2) ) ),
    inference(duplicate_literal_removal,[],[f710])).

fof(f710,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X2,X2),X3)
      | k3_xboole_0(X2,X2) = k3_xboole_0(X3,X2)
      | ~ r1_tarski(k3_xboole_0(X2,X2),X2)
      | k3_xboole_0(X2,X2) = k3_xboole_0(X3,X2)
      | ~ r1_tarski(k3_xboole_0(X2,X2),X2)
      | ~ r1_tarski(k3_xboole_0(X2,X2),X3) ) ),
    inference(resolution,[],[f159,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK4(X0,X1,X2),X0)
        & r1_tarski(sK4(X0,X1,X2),X2)
        & r1_tarski(sK4(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK4(X0,X1,X2),X0)
        & r1_tarski(sK4(X0,X1,X2),X2)
        & r1_tarski(sK4(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f159,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(sK4(k3_xboole_0(X3,X4),X5,X4),X3)
      | ~ r1_tarski(k3_xboole_0(X3,X4),X5)
      | k3_xboole_0(X5,X4) = k3_xboole_0(X3,X4)
      | ~ r1_tarski(k3_xboole_0(X3,X4),X4) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k3_xboole_0(X3,X4),X4)
      | ~ r1_tarski(k3_xboole_0(X3,X4),X5)
      | k3_xboole_0(X5,X4) = k3_xboole_0(X3,X4)
      | ~ r1_tarski(sK4(k3_xboole_0(X3,X4),X5,X4),X3)
      | k3_xboole_0(X5,X4) = k3_xboole_0(X3,X4)
      | ~ r1_tarski(k3_xboole_0(X3,X4),X4)
      | ~ r1_tarski(k3_xboole_0(X3,X4),X5) ) ),
    inference(resolution,[],[f71,f34])).

fof(f71,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_tarski(sK4(k3_xboole_0(X10,X11),X8,X9),X11)
      | ~ r1_tarski(k3_xboole_0(X10,X11),X9)
      | ~ r1_tarski(k3_xboole_0(X10,X11),X8)
      | k3_xboole_0(X8,X9) = k3_xboole_0(X10,X11)
      | ~ r1_tarski(sK4(k3_xboole_0(X10,X11),X8,X9),X10) ) ),
    inference(resolution,[],[f35,f32])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK4(X0,X1,X2),X0)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9065,plain,
    ( ! [X14,X13] : r1_tarski(k3_xboole_0(sK0,X13),k3_xboole_0(k2_xboole_0(sK1,X14),X13))
    | ~ spl5_33 ),
    inference(resolution,[],[f9033,f263])).

fof(f263,plain,(
    ! [X28,X26,X27,X25] :
      ( ~ r1_tarski(X25,k3_xboole_0(X27,X28))
      | r1_tarski(k3_xboole_0(X25,X26),k3_xboole_0(X27,X26)) ) ),
    inference(resolution,[],[f119,f28])).

fof(f119,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_tarski(X4,X6)
      | r1_tarski(k3_xboole_0(X3,X5),k3_xboole_0(X6,X5))
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f56,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k3_xboole_0(X1,X2),X3)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),X3) ) ),
    inference(resolution,[],[f30,f31])).

fof(f9033,plain,
    ( ! [X0] : r1_tarski(sK0,k3_xboole_0(k2_xboole_0(sK1,X0),sK1))
    | ~ spl5_33 ),
    inference(resolution,[],[f8385,f27])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f8385,plain,
    ( ! [X20] :
        ( ~ r1_tarski(sK1,X20)
        | r1_tarski(sK0,k3_xboole_0(X20,sK1)) )
    | ~ spl5_33 ),
    inference(resolution,[],[f7638,f30])).

fof(f7638,plain,
    ( ! [X19] :
        ( ~ r1_tarski(k3_xboole_0(sK1,sK1),X19)
        | r1_tarski(sK0,X19) )
    | ~ spl5_33 ),
    inference(resolution,[],[f7458,f31])).

fof(f7458,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,sK1))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f7456])).

fof(f7542,plain,
    ( spl5_34
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f7274,f42,f7539])).

fof(f7539,plain,
    ( spl5_34
  <=> r1_tarski(sK2,k3_xboole_0(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f7274,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK3,sK3))
    | ~ spl5_2 ),
    inference(resolution,[],[f5509,f44])).

fof(f5509,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k3_xboole_0(X1,X1)) ) ),
    inference(condensation,[],[f5422])).

fof(f5422,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X1))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f607,f28])).

fof(f607,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k3_xboole_0(X2,X1),X3)
      | r1_tarski(X0,k3_xboole_0(X2,X3))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f132,f28])).

fof(f132,plain,(
    ! [X24,X23,X21,X25,X22] :
      ( ~ r1_tarski(k3_xboole_0(X22,X23),X24)
      | ~ r1_tarski(X21,X23)
      | r1_tarski(X21,k3_xboole_0(X24,X25))
      | ~ r1_tarski(k3_xboole_0(X22,X23),X25)
      | ~ r1_tarski(X21,X22) ) ),
    inference(resolution,[],[f60,f32])).

fof(f7459,plain,
    ( spl5_33
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f7263,f37,f7456])).

fof(f37,plain,
    ( spl5_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f7263,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f5509,f39])).

fof(f39,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f5554,plain,
    ( spl5_32
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f3955,f3857,f5551])).

fof(f5551,plain,
    ( spl5_32
  <=> k3_xboole_0(sK2,sK2) = k3_xboole_0(k3_xboole_0(sK3,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f3857,plain,
    ( spl5_28
  <=> r1_tarski(k3_xboole_0(sK2,sK2),k3_xboole_0(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f3955,plain,
    ( k3_xboole_0(sK2,sK2) = k3_xboole_0(k3_xboole_0(sK3,sK3),sK2)
    | ~ spl5_28 ),
    inference(resolution,[],[f3859,f721])).

fof(f3859,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK2),k3_xboole_0(sK3,sK3))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f3857])).

fof(f5549,plain,
    ( spl5_31
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f3954,f3857,f5546])).

fof(f5546,plain,
    ( spl5_31
  <=> k3_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f3954,plain,
    ( k3_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK3,sK3))
    | ~ spl5_28 ),
    inference(resolution,[],[f3859,f734])).

fof(f734,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X0,X0),X1)
      | k3_xboole_0(X0,X1) = k3_xboole_0(X0,X0) ) ),
    inference(subsumption_resolution,[],[f733,f28])).

fof(f733,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X0,X0),X0)
      | k3_xboole_0(X0,X1) = k3_xboole_0(X0,X0)
      | ~ r1_tarski(k3_xboole_0(X0,X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f722])).

fof(f722,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X0,X0),X0)
      | k3_xboole_0(X0,X1) = k3_xboole_0(X0,X0)
      | ~ r1_tarski(k3_xboole_0(X0,X0),X1)
      | k3_xboole_0(X0,X1) = k3_xboole_0(X0,X0)
      | ~ r1_tarski(k3_xboole_0(X0,X0),X1)
      | ~ r1_tarski(k3_xboole_0(X0,X0),X0) ) ),
    inference(resolution,[],[f160,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK4(X0,X1,X2),X1)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK4(k3_xboole_0(X0,X1),X1,X2),X0)
      | ~ r1_tarski(k3_xboole_0(X0,X1),X1)
      | k3_xboole_0(X0,X1) = k3_xboole_0(X1,X2)
      | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k3_xboole_0(X0,X1),X1)
      | k3_xboole_0(X0,X1) = k3_xboole_0(X1,X2)
      | ~ r1_tarski(sK4(k3_xboole_0(X0,X1),X1,X2),X0)
      | k3_xboole_0(X0,X1) = k3_xboole_0(X1,X2)
      | ~ r1_tarski(k3_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f71,f33])).

fof(f5544,plain,
    ( spl5_30
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f3521,f3439,f5541])).

fof(f5541,plain,
    ( spl5_30
  <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(k3_xboole_0(sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f3439,plain,
    ( spl5_27
  <=> r1_tarski(k3_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f3521,plain,
    ( k3_xboole_0(sK0,sK0) = k3_xboole_0(k3_xboole_0(sK1,sK1),sK0)
    | ~ spl5_27 ),
    inference(resolution,[],[f3441,f721])).

fof(f3441,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK1))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f3439])).

fof(f5421,plain,
    ( spl5_29
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f3520,f3439,f5418])).

fof(f5418,plain,
    ( spl5_29
  <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f3520,plain,
    ( k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1))
    | ~ spl5_27 ),
    inference(resolution,[],[f3441,f734])).

fof(f3860,plain,
    ( spl5_28
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f3791,f3158,f42,f3857])).

fof(f3158,plain,
    ( spl5_26
  <=> k3_xboole_0(sK2,sK2) = k3_xboole_0(k3_xboole_0(sK2,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f3791,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK2),k3_xboole_0(sK3,sK3))
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(superposition,[],[f999,f3160])).

fof(f3160,plain,
    ( k3_xboole_0(sK2,sK2) = k3_xboole_0(k3_xboole_0(sK2,sK2),sK3)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f3158])).

fof(f999,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(k3_xboole_0(sK2,X0),X1),k3_xboole_0(sK3,X1))
    | ~ spl5_2 ),
    inference(resolution,[],[f275,f28])).

fof(f275,plain,
    ( ! [X70,X71] :
        ( ~ r1_tarski(X70,sK2)
        | r1_tarski(k3_xboole_0(X70,X71),k3_xboole_0(sK3,X71)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f119,f44])).

fof(f3442,plain,
    ( spl5_27
    | ~ spl5_1
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f3299,f3146,f37,f3439])).

fof(f3146,plain,
    ( spl5_25
  <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(k3_xboole_0(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f3299,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK1))
    | ~ spl5_1
    | ~ spl5_25 ),
    inference(superposition,[],[f975,f3148])).

fof(f3148,plain,
    ( k3_xboole_0(sK0,sK0) = k3_xboole_0(k3_xboole_0(sK0,sK0),sK1)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f3146])).

fof(f975,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X0),X1),k3_xboole_0(sK1,X1))
    | ~ spl5_1 ),
    inference(resolution,[],[f270,f28])).

fof(f270,plain,
    ( ! [X54,X53] :
        ( ~ r1_tarski(X53,sK0)
        | r1_tarski(k3_xboole_0(X53,X54),k3_xboole_0(sK1,X54)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f119,f39])).

fof(f3161,plain,
    ( spl5_26
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f3064,f42,f3158])).

fof(f3064,plain,
    ( k3_xboole_0(sK2,sK2) = k3_xboole_0(k3_xboole_0(sK2,sK2),sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f559,f491])).

fof(f559,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X0,X0),X1)
      | k3_xboole_0(X0,X0) = k3_xboole_0(k3_xboole_0(X0,X0),X1) ) ),
    inference(resolution,[],[f116,f28])).

fof(f116,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k3_xboole_0(X3,X4),X4)
      | k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X5)
      | ~ r1_tarski(k3_xboole_0(X3,X4),X5) ) ),
    inference(subsumption_resolution,[],[f113,f28])).

fof(f113,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k3_xboole_0(X3,X4),X5)
      | k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X5)
      | ~ r1_tarski(k3_xboole_0(X3,X4),X4)
      | ~ r1_tarski(k3_xboole_0(X3,X4),X3) ) ),
    inference(resolution,[],[f73,f32])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X0)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0)
      | k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f35,f33])).

fof(f3149,plain,
    ( spl5_25
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f3059,f37,f3146])).

fof(f3059,plain,
    ( k3_xboole_0(sK0,sK0) = k3_xboole_0(k3_xboole_0(sK0,sK0),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f559,f850])).

fof(f850,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f810,f28])).

fof(f810,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl5_1 ),
    inference(condensation,[],[f798])).

fof(f798,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f786,f32])).

fof(f786,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k3_xboole_0(sK0,X1))
        | r1_tarski(X0,sK1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f308,f28])).

fof(f308,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK0)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(X0,sK1) )
    | ~ spl5_1 ),
    inference(condensation,[],[f303])).

fof(f303,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X1,sK1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f229,f60])).

fof(f229,plain,
    ( ! [X47,X48] :
        ( r1_tarski(k3_xboole_0(X47,X48),sK1)
        | ~ r1_tarski(X47,sK0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f79,f39])).

fof(f3094,plain,
    ( spl5_24
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f3005,f42,f3091])).

fof(f3091,plain,
    ( spl5_24
  <=> k3_xboole_0(sK2,sK2) = k3_xboole_0(sK3,k3_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f3005,plain,
    ( k3_xboole_0(sK2,sK2) = k3_xboole_0(sK3,k3_xboole_0(sK2,sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f520,f491])).

fof(f520,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X0,X0),X1)
      | k3_xboole_0(X0,X0) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ) ),
    inference(resolution,[],[f111,f28])).

fof(f111,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k3_xboole_0(X4,X5),X5)
      | ~ r1_tarski(k3_xboole_0(X4,X5),X3)
      | k3_xboole_0(X4,X5) = k3_xboole_0(X3,k3_xboole_0(X4,X5)) ) ),
    inference(subsumption_resolution,[],[f108,f28])).

fof(f108,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X4,X5) = k3_xboole_0(X3,k3_xboole_0(X4,X5))
      | ~ r1_tarski(k3_xboole_0(X4,X5),X3)
      | ~ r1_tarski(k3_xboole_0(X4,X5),X5)
      | ~ r1_tarski(k3_xboole_0(X4,X5),X4) ) ),
    inference(resolution,[],[f72,f32])).

fof(f72,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X3)
      | k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2)
      | k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f35,f34])).

fof(f3035,plain,
    ( spl5_23
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f3000,f37,f3032])).

fof(f3032,plain,
    ( spl5_23
  <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f3000,plain,
    ( k3_xboole_0(sK0,sK0) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f520,f850])).

fof(f2196,plain,
    ( spl5_21
    | ~ spl5_22
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f355,f86,f2193,f2190])).

fof(f2190,plain,
    ( spl5_21
  <=> ! [X46] :
        ( ~ r1_tarski(sK1,X46)
        | sK1 = k3_xboole_0(k3_xboole_0(sK0,sK2),X46) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f2193,plain,
    ( spl5_22
  <=> r1_tarski(sK1,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f86,plain,
    ( spl5_5
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f355,plain,
    ( ! [X46] :
        ( ~ r1_tarski(sK1,k3_xboole_0(sK0,sK2))
        | ~ r1_tarski(sK1,X46)
        | sK1 = k3_xboole_0(k3_xboole_0(sK0,sK2),X46) )
    | ~ spl5_5 ),
    inference(resolution,[],[f138,f87])).

fof(f87,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X2,X1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X2,X0)
      | k3_xboole_0(X2,X1) = X0
      | k3_xboole_0(X2,X1) = X0
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f63,f35])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(sK4(X2,X0,X1),X3)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X0,X3)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(resolution,[],[f33,f31])).

fof(f2188,plain,
    ( spl5_20
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1985,f42,f2185])).

fof(f2185,plain,
    ( spl5_20
  <=> k3_xboole_0(sK2,sK2) = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1985,plain,
    ( k3_xboole_0(sK2,sK2) = k3_xboole_0(sK2,sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f734,f491])).

fof(f2168,plain,
    ( spl5_19
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f1981,f37,f2165])).

fof(f2165,plain,
    ( spl5_19
  <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1981,plain,
    ( k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f734,f850])).

fof(f2070,plain,
    ( spl5_18
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1941,f42,f2067])).

fof(f2067,plain,
    ( spl5_18
  <=> k3_xboole_0(sK3,sK2) = k3_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1941,plain,
    ( k3_xboole_0(sK3,sK2) = k3_xboole_0(sK2,sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f721,f491])).

fof(f1962,plain,
    ( spl5_17
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f1937,f37,f1959])).

fof(f1959,plain,
    ( spl5_17
  <=> k3_xboole_0(sK1,sK0) = k3_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f1937,plain,
    ( k3_xboole_0(sK1,sK0) = k3_xboole_0(sK0,sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f721,f850])).

fof(f1206,plain,
    ( spl5_15
    | ~ spl5_16
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f362,f42,f1203,f1200])).

fof(f1200,plain,
    ( spl5_15
  <=> ! [X61] :
        ( ~ r1_tarski(sK3,X61)
        | sK3 = k3_xboole_0(sK2,X61) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f1203,plain,
    ( spl5_16
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f362,plain,
    ( ! [X61] :
        ( ~ r1_tarski(sK3,sK2)
        | ~ r1_tarski(sK3,X61)
        | sK3 = k3_xboole_0(sK2,X61) )
    | ~ spl5_2 ),
    inference(resolution,[],[f138,f44])).

fof(f1198,plain,
    ( spl5_13
    | ~ spl5_14
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f357,f37,f1195,f1192])).

fof(f1192,plain,
    ( spl5_13
  <=> ! [X49] :
        ( ~ r1_tarski(sK1,X49)
        | sK1 = k3_xboole_0(sK0,X49) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1195,plain,
    ( spl5_14
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f357,plain,
    ( ! [X49] :
        ( ~ r1_tarski(sK1,sK0)
        | ~ r1_tarski(sK1,X49)
        | sK1 = k3_xboole_0(sK0,X49) )
    | ~ spl5_1 ),
    inference(resolution,[],[f138,f39])).

fof(f825,plain,
    ( spl5_11
    | ~ spl5_12
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f808,f42,f37,f822,f818])).

fof(f818,plain,
    ( spl5_11
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f822,plain,
    ( spl5_12
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f808,plain,
    ( ~ r1_tarski(sK3,sK0)
    | r1_tarski(sK2,sK1)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(condensation,[],[f803])).

fof(f803,plain,
    ( ! [X10] :
        ( r1_tarski(sK2,sK1)
        | ~ r1_tarski(sK3,X10)
        | ~ r1_tarski(sK3,sK0) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f786,f67])).

fof(f67,plain,
    ( ! [X4,X3] :
        ( r1_tarski(sK2,k3_xboole_0(X3,X4))
        | ~ r1_tarski(sK3,X4)
        | ~ r1_tarski(sK3,X3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f55,f32])).

fof(f55,plain,
    ( ! [X11] :
        ( ~ r1_tarski(sK3,X11)
        | r1_tarski(sK2,X11) )
    | ~ spl5_2 ),
    inference(resolution,[],[f31,f44])).

fof(f466,plain,
    ( ~ spl5_10
    | ~ spl5_1
    | ~ spl5_2
    | spl5_7 ),
    inference(avatar_split_clause,[],[f427,f100,f42,f37,f463])).

fof(f463,plain,
    ( spl5_10
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f100,plain,
    ( spl5_7
  <=> r1_tarski(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f427,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_7 ),
    inference(subsumption_resolution,[],[f425,f102])).

fof(f102,plain,
    ( ~ r1_tarski(sK0,sK3)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f425,plain,
    ( ~ r1_tarski(sK1,sK2)
    | r1_tarski(sK0,sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(condensation,[],[f418])).

fof(f418,plain,
    ( ! [X9] :
        ( r1_tarski(sK0,sK3)
        | ~ r1_tarski(sK1,sK2)
        | ~ r1_tarski(sK1,X9) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f407,f61])).

fof(f61,plain,
    ( ! [X4,X5] :
        ( r1_tarski(sK0,k3_xboole_0(X5,X4))
        | ~ r1_tarski(sK1,X5)
        | ~ r1_tarski(sK1,X4) )
    | ~ spl5_1 ),
    inference(resolution,[],[f32,f54])).

fof(f54,plain,
    ( ! [X10] :
        ( ~ r1_tarski(sK1,X10)
        | r1_tarski(sK0,X10) )
    | ~ spl5_1 ),
    inference(resolution,[],[f31,f39])).

fof(f197,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f187,f81,f37,f194,f190])).

fof(f190,plain,
    ( spl5_8
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f194,plain,
    ( spl5_9
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f81,plain,
    ( spl5_4
  <=> r1_tarski(sK0,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f187,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,sK3)
    | ~ spl5_1
    | spl5_4 ),
    inference(resolution,[],[f61,f83])).

fof(f83,plain,
    ( ~ r1_tarski(sK0,k3_xboole_0(sK1,sK3))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f103,plain,
    ( ~ spl5_7
    | spl5_6 ),
    inference(avatar_split_clause,[],[f98,f90,f100])).

fof(f98,plain,
    ( ~ r1_tarski(sK0,sK3)
    | spl5_6 ),
    inference(resolution,[],[f92,f53])).

fof(f96,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f94,f39])).

fof(f94,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl5_5 ),
    inference(resolution,[],[f88,f53])).

fof(f88,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f93,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_3 ),
    inference(avatar_split_clause,[],[f59,f47,f90,f86])).

fof(f47,plain,
    ( spl5_3
  <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f59,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(resolution,[],[f32,f49])).

fof(f49,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f84,plain,
    ( ~ spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f78,f47,f81])).

fof(f78,plain,
    ( ~ r1_tarski(sK0,k3_xboole_0(sK1,sK3))
    | spl5_3 ),
    inference(resolution,[],[f53,f49])).

fof(f50,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

fof(f45,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f24,f37])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (21841)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (21835)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.43  % (21837)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.43  % (21839)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.44  % (21843)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.44  % (21842)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.44  % (21838)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.45  % (21840)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.45  % (21836)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.46  % (21844)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.46  % (21834)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.48  % (21845)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 5.23/1.02  % (21835)Time limit reached!
% 5.23/1.02  % (21835)------------------------------
% 5.23/1.02  % (21835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.23/1.02  % (21835)Termination reason: Time limit
% 5.23/1.02  % (21835)Termination phase: Saturation
% 5.23/1.02  
% 5.23/1.02  % (21835)Memory used [KB]: 17910
% 5.23/1.02  % (21835)Time elapsed: 0.600 s
% 5.23/1.02  % (21835)------------------------------
% 5.23/1.02  % (21835)------------------------------
% 8.32/1.42  % (21834)Time limit reached!
% 8.32/1.42  % (21834)------------------------------
% 8.32/1.42  % (21834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.32/1.42  % (21834)Termination reason: Time limit
% 8.32/1.42  % (21834)Termination phase: Saturation
% 8.32/1.42  
% 8.32/1.42  % (21834)Memory used [KB]: 16630
% 8.32/1.42  % (21834)Time elapsed: 1.0000 s
% 8.32/1.42  % (21834)------------------------------
% 8.32/1.42  % (21834)------------------------------
% 16.56/2.44  % (21840)Refutation found. Thanks to Tanya!
% 16.56/2.44  % SZS status Theorem for theBenchmark
% 16.56/2.44  % SZS output start Proof for theBenchmark
% 16.56/2.44  fof(f12501,plain,(
% 16.56/2.44    $false),
% 16.56/2.44    inference(avatar_sat_refutation,[],[f40,f45,f50,f84,f93,f96,f103,f197,f466,f825,f1198,f1206,f1962,f2070,f2168,f2188,f2196,f3035,f3094,f3149,f3161,f3442,f3860,f5421,f5544,f5549,f5554,f7459,f7542,f12328,f12498])).
% 16.56/2.44  fof(f12498,plain,(
% 16.56/2.44    ~spl5_2 | spl5_6 | ~spl5_35),
% 16.56/2.44    inference(avatar_contradiction_clause,[],[f12497])).
% 16.56/2.44  fof(f12497,plain,(
% 16.56/2.44    $false | (~spl5_2 | spl5_6 | ~spl5_35)),
% 16.56/2.44    inference(subsumption_resolution,[],[f12440,f92])).
% 16.56/2.44  fof(f92,plain,(
% 16.56/2.44    ~r1_tarski(k3_xboole_0(sK0,sK2),sK3) | spl5_6),
% 16.56/2.44    inference(avatar_component_clause,[],[f90])).
% 16.56/2.44  fof(f90,plain,(
% 16.56/2.44    spl5_6 <=> r1_tarski(k3_xboole_0(sK0,sK2),sK3)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 16.56/2.44  fof(f12440,plain,(
% 16.56/2.44    r1_tarski(k3_xboole_0(sK0,sK2),sK3) | (~spl5_2 | ~spl5_35)),
% 16.56/2.44    inference(resolution,[],[f12327,f407])).
% 16.56/2.44  fof(f407,plain,(
% 16.56/2.44    ( ! [X0,X1] : (~r1_tarski(X0,k3_xboole_0(sK2,X1)) | r1_tarski(X0,sK3)) ) | ~spl5_2),
% 16.56/2.44    inference(condensation,[],[f399])).
% 16.56/2.44  fof(f399,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(sK2,X1)) | ~r1_tarski(X0,X2) | r1_tarski(X0,sK3)) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f337,f60])).
% 16.56/2.44  fof(f60,plain,(
% 16.56/2.44    ( ! [X2,X0,X3,X1] : (~r1_tarski(k3_xboole_0(X2,X1),X3) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X3)) )),
% 16.56/2.44    inference(resolution,[],[f32,f31])).
% 16.56/2.44  fof(f31,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 16.56/2.44    inference(cnf_transformation,[],[f15])).
% 16.56/2.44  fof(f15,plain,(
% 16.56/2.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 16.56/2.44    inference(flattening,[],[f14])).
% 16.56/2.44  fof(f14,plain,(
% 16.56/2.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 16.56/2.44    inference(ennf_transformation,[],[f4])).
% 16.56/2.44  fof(f4,axiom,(
% 16.56/2.44    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 16.56/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 16.56/2.44  fof(f32,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 16.56/2.44    inference(cnf_transformation,[],[f17])).
% 16.56/2.44  fof(f17,plain,(
% 16.56/2.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 16.56/2.44    inference(flattening,[],[f16])).
% 16.56/2.44  fof(f16,plain,(
% 16.56/2.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 16.56/2.44    inference(ennf_transformation,[],[f3])).
% 16.56/2.44  fof(f3,axiom,(
% 16.56/2.44    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 16.56/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 16.56/2.44  fof(f337,plain,(
% 16.56/2.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k3_xboole_0(sK2,X0),X1),sK3)) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f233,f28])).
% 16.56/2.44  fof(f28,plain,(
% 16.56/2.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 16.56/2.44    inference(cnf_transformation,[],[f2])).
% 16.56/2.44  fof(f2,axiom,(
% 16.56/2.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 16.56/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 16.56/2.44  fof(f233,plain,(
% 16.56/2.44    ( ! [X61,X60] : (~r1_tarski(X60,sK2) | r1_tarski(k3_xboole_0(X60,X61),sK3)) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f79,f44])).
% 16.56/2.44  fof(f44,plain,(
% 16.56/2.44    r1_tarski(sK2,sK3) | ~spl5_2),
% 16.56/2.44    inference(avatar_component_clause,[],[f42])).
% 16.56/2.44  fof(f42,plain,(
% 16.56/2.44    spl5_2 <=> r1_tarski(sK2,sK3)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 16.56/2.44  fof(f79,plain,(
% 16.56/2.44    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X3),X2)) )),
% 16.56/2.44    inference(resolution,[],[f53,f31])).
% 16.56/2.44  fof(f53,plain,(
% 16.56/2.44    ( ! [X8,X7,X9] : (r1_tarski(k3_xboole_0(X7,X9),X8) | ~r1_tarski(X7,X8)) )),
% 16.56/2.44    inference(resolution,[],[f31,f28])).
% 16.56/2.44  fof(f12327,plain,(
% 16.56/2.44    r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,sK2)) | ~spl5_35),
% 16.56/2.44    inference(avatar_component_clause,[],[f12325])).
% 16.56/2.44  fof(f12325,plain,(
% 16.56/2.44    spl5_35 <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,sK2))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 16.56/2.44  fof(f12328,plain,(
% 16.56/2.44    spl5_35 | ~spl5_2 | ~spl5_33),
% 16.56/2.44    inference(avatar_split_clause,[],[f12197,f7456,f42,f12325])).
% 16.56/2.44  fof(f7456,plain,(
% 16.56/2.44    spl5_33 <=> r1_tarski(sK0,k3_xboole_0(sK1,sK1))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 16.56/2.44  fof(f12197,plain,(
% 16.56/2.44    r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK2,sK2)) | (~spl5_2 | ~spl5_33)),
% 16.56/2.44    inference(superposition,[],[f9065,f1943])).
% 16.56/2.44  fof(f1943,plain,(
% 16.56/2.44    ( ! [X39] : (k3_xboole_0(sK2,sK2) = k3_xboole_0(k2_xboole_0(X39,sK3),sK2)) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f721,f569])).
% 16.56/2.44  fof(f569,plain,(
% 16.56/2.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(sK2,X0),k2_xboole_0(X1,sK3))) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f512,f28])).
% 16.56/2.44  fof(f512,plain,(
% 16.56/2.44    ( ! [X0,X1] : (~r1_tarski(X0,sK2) | r1_tarski(X0,k2_xboole_0(X1,sK3))) ) | ~spl5_2),
% 16.56/2.44    inference(condensation,[],[f501])).
% 16.56/2.44  fof(f501,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,sK3)) | ~r1_tarski(X0,sK2)) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f491,f131])).
% 16.56/2.44  fof(f131,plain,(
% 16.56/2.44    ( ! [X19,X17,X20,X18,X16] : (~r1_tarski(k3_xboole_0(X17,X18),X20) | ~r1_tarski(X16,X18) | r1_tarski(X16,k2_xboole_0(X19,X20)) | ~r1_tarski(X16,X17)) )),
% 16.56/2.44    inference(resolution,[],[f60,f29])).
% 16.56/2.44  fof(f29,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 16.56/2.44    inference(cnf_transformation,[],[f12])).
% 16.56/2.44  fof(f12,plain,(
% 16.56/2.44    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 16.56/2.44    inference(ennf_transformation,[],[f1])).
% 16.56/2.44  fof(f1,axiom,(
% 16.56/2.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 16.56/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 16.56/2.44  fof(f491,plain,(
% 16.56/2.44    ( ! [X0] : (r1_tarski(k3_xboole_0(sK2,X0),sK3)) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f426,f28])).
% 16.56/2.44  fof(f426,plain,(
% 16.56/2.44    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,sK3)) ) | ~spl5_2),
% 16.56/2.44    inference(condensation,[],[f414])).
% 16.56/2.44  fof(f414,plain,(
% 16.56/2.44    ( ! [X0,X1] : (r1_tarski(X0,sK3) | ~r1_tarski(X0,X1) | ~r1_tarski(X0,sK2)) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f407,f32])).
% 16.56/2.44  fof(f721,plain,(
% 16.56/2.44    ( ! [X2,X3] : (~r1_tarski(k3_xboole_0(X2,X2),X3) | k3_xboole_0(X2,X2) = k3_xboole_0(X3,X2)) )),
% 16.56/2.44    inference(subsumption_resolution,[],[f719,f28])).
% 16.56/2.44  fof(f719,plain,(
% 16.56/2.44    ( ! [X2,X3] : (~r1_tarski(k3_xboole_0(X2,X2),X3) | k3_xboole_0(X2,X2) = k3_xboole_0(X3,X2) | ~r1_tarski(k3_xboole_0(X2,X2),X2)) )),
% 16.56/2.44    inference(duplicate_literal_removal,[],[f710])).
% 16.56/2.44  fof(f710,plain,(
% 16.56/2.44    ( ! [X2,X3] : (~r1_tarski(k3_xboole_0(X2,X2),X3) | k3_xboole_0(X2,X2) = k3_xboole_0(X3,X2) | ~r1_tarski(k3_xboole_0(X2,X2),X2) | k3_xboole_0(X2,X2) = k3_xboole_0(X3,X2) | ~r1_tarski(k3_xboole_0(X2,X2),X2) | ~r1_tarski(k3_xboole_0(X2,X2),X3)) )),
% 16.56/2.44    inference(resolution,[],[f159,f34])).
% 16.56/2.44  fof(f34,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (r1_tarski(sK4(X0,X1,X2),X2) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 16.56/2.44    inference(cnf_transformation,[],[f23])).
% 16.56/2.44  fof(f23,plain,(
% 16.56/2.44    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK4(X0,X1,X2),X0) & r1_tarski(sK4(X0,X1,X2),X2) & r1_tarski(sK4(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 16.56/2.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f22])).
% 16.56/2.44  fof(f22,plain,(
% 16.56/2.44    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK4(X0,X1,X2),X0) & r1_tarski(sK4(X0,X1,X2),X2) & r1_tarski(sK4(X0,X1,X2),X1)))),
% 16.56/2.44    introduced(choice_axiom,[])).
% 16.56/2.44  fof(f19,plain,(
% 16.56/2.44    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 16.56/2.44    inference(flattening,[],[f18])).
% 16.56/2.44  fof(f18,plain,(
% 16.56/2.44    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 16.56/2.44    inference(ennf_transformation,[],[f5])).
% 16.56/2.44  fof(f5,axiom,(
% 16.56/2.44    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 16.56/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 16.56/2.44  fof(f159,plain,(
% 16.56/2.44    ( ! [X4,X5,X3] : (~r1_tarski(sK4(k3_xboole_0(X3,X4),X5,X4),X3) | ~r1_tarski(k3_xboole_0(X3,X4),X5) | k3_xboole_0(X5,X4) = k3_xboole_0(X3,X4) | ~r1_tarski(k3_xboole_0(X3,X4),X4)) )),
% 16.56/2.44    inference(duplicate_literal_removal,[],[f152])).
% 16.56/2.44  fof(f152,plain,(
% 16.56/2.44    ( ! [X4,X5,X3] : (~r1_tarski(k3_xboole_0(X3,X4),X4) | ~r1_tarski(k3_xboole_0(X3,X4),X5) | k3_xboole_0(X5,X4) = k3_xboole_0(X3,X4) | ~r1_tarski(sK4(k3_xboole_0(X3,X4),X5,X4),X3) | k3_xboole_0(X5,X4) = k3_xboole_0(X3,X4) | ~r1_tarski(k3_xboole_0(X3,X4),X4) | ~r1_tarski(k3_xboole_0(X3,X4),X5)) )),
% 16.56/2.44    inference(resolution,[],[f71,f34])).
% 16.56/2.44  fof(f71,plain,(
% 16.56/2.44    ( ! [X10,X8,X11,X9] : (~r1_tarski(sK4(k3_xboole_0(X10,X11),X8,X9),X11) | ~r1_tarski(k3_xboole_0(X10,X11),X9) | ~r1_tarski(k3_xboole_0(X10,X11),X8) | k3_xboole_0(X8,X9) = k3_xboole_0(X10,X11) | ~r1_tarski(sK4(k3_xboole_0(X10,X11),X8,X9),X10)) )),
% 16.56/2.44    inference(resolution,[],[f35,f32])).
% 16.56/2.44  fof(f35,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (~r1_tarski(sK4(X0,X1,X2),X0) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 16.56/2.44    inference(cnf_transformation,[],[f23])).
% 16.56/2.44  fof(f9065,plain,(
% 16.56/2.44    ( ! [X14,X13] : (r1_tarski(k3_xboole_0(sK0,X13),k3_xboole_0(k2_xboole_0(sK1,X14),X13))) ) | ~spl5_33),
% 16.56/2.44    inference(resolution,[],[f9033,f263])).
% 16.56/2.44  fof(f263,plain,(
% 16.56/2.44    ( ! [X28,X26,X27,X25] : (~r1_tarski(X25,k3_xboole_0(X27,X28)) | r1_tarski(k3_xboole_0(X25,X26),k3_xboole_0(X27,X26))) )),
% 16.56/2.44    inference(resolution,[],[f119,f28])).
% 16.56/2.44  fof(f119,plain,(
% 16.56/2.44    ( ! [X6,X4,X5,X3] : (~r1_tarski(X4,X6) | r1_tarski(k3_xboole_0(X3,X5),k3_xboole_0(X6,X5)) | ~r1_tarski(X3,X4)) )),
% 16.56/2.44    inference(resolution,[],[f56,f30])).
% 16.56/2.44  fof(f30,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 16.56/2.44    inference(cnf_transformation,[],[f13])).
% 16.56/2.44  fof(f13,plain,(
% 16.56/2.44    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 16.56/2.44    inference(ennf_transformation,[],[f6])).
% 16.56/2.44  fof(f6,axiom,(
% 16.56/2.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 16.56/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).
% 16.56/2.44  fof(f56,plain,(
% 16.56/2.44    ( ! [X2,X0,X3,X1] : (~r1_tarski(k3_xboole_0(X1,X2),X3) | ~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X3)) )),
% 16.56/2.44    inference(resolution,[],[f30,f31])).
% 16.56/2.44  fof(f9033,plain,(
% 16.56/2.44    ( ! [X0] : (r1_tarski(sK0,k3_xboole_0(k2_xboole_0(sK1,X0),sK1))) ) | ~spl5_33),
% 16.56/2.44    inference(resolution,[],[f8385,f27])).
% 16.56/2.44  fof(f27,plain,(
% 16.56/2.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 16.56/2.44    inference(cnf_transformation,[],[f7])).
% 16.56/2.44  fof(f7,axiom,(
% 16.56/2.44    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 16.56/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 16.56/2.44  fof(f8385,plain,(
% 16.56/2.44    ( ! [X20] : (~r1_tarski(sK1,X20) | r1_tarski(sK0,k3_xboole_0(X20,sK1))) ) | ~spl5_33),
% 16.56/2.44    inference(resolution,[],[f7638,f30])).
% 16.56/2.44  fof(f7638,plain,(
% 16.56/2.44    ( ! [X19] : (~r1_tarski(k3_xboole_0(sK1,sK1),X19) | r1_tarski(sK0,X19)) ) | ~spl5_33),
% 16.56/2.44    inference(resolution,[],[f7458,f31])).
% 16.56/2.44  fof(f7458,plain,(
% 16.56/2.44    r1_tarski(sK0,k3_xboole_0(sK1,sK1)) | ~spl5_33),
% 16.56/2.44    inference(avatar_component_clause,[],[f7456])).
% 16.56/2.44  fof(f7542,plain,(
% 16.56/2.44    spl5_34 | ~spl5_2),
% 16.56/2.44    inference(avatar_split_clause,[],[f7274,f42,f7539])).
% 16.56/2.44  fof(f7539,plain,(
% 16.56/2.44    spl5_34 <=> r1_tarski(sK2,k3_xboole_0(sK3,sK3))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 16.56/2.44  fof(f7274,plain,(
% 16.56/2.44    r1_tarski(sK2,k3_xboole_0(sK3,sK3)) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f5509,f44])).
% 16.56/2.44  fof(f5509,plain,(
% 16.56/2.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k3_xboole_0(X1,X1))) )),
% 16.56/2.44    inference(condensation,[],[f5422])).
% 16.56/2.44  fof(f5422,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 16.56/2.44    inference(resolution,[],[f607,f28])).
% 16.56/2.44  fof(f607,plain,(
% 16.56/2.44    ( ! [X2,X0,X3,X1] : (~r1_tarski(k3_xboole_0(X2,X1),X3) | r1_tarski(X0,k3_xboole_0(X2,X3)) | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X2)) )),
% 16.56/2.44    inference(resolution,[],[f132,f28])).
% 16.56/2.44  fof(f132,plain,(
% 16.56/2.44    ( ! [X24,X23,X21,X25,X22] : (~r1_tarski(k3_xboole_0(X22,X23),X24) | ~r1_tarski(X21,X23) | r1_tarski(X21,k3_xboole_0(X24,X25)) | ~r1_tarski(k3_xboole_0(X22,X23),X25) | ~r1_tarski(X21,X22)) )),
% 16.56/2.44    inference(resolution,[],[f60,f32])).
% 16.56/2.44  fof(f7459,plain,(
% 16.56/2.44    spl5_33 | ~spl5_1),
% 16.56/2.44    inference(avatar_split_clause,[],[f7263,f37,f7456])).
% 16.56/2.44  fof(f37,plain,(
% 16.56/2.44    spl5_1 <=> r1_tarski(sK0,sK1)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 16.56/2.44  fof(f7263,plain,(
% 16.56/2.44    r1_tarski(sK0,k3_xboole_0(sK1,sK1)) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f5509,f39])).
% 16.56/2.44  fof(f39,plain,(
% 16.56/2.44    r1_tarski(sK0,sK1) | ~spl5_1),
% 16.56/2.44    inference(avatar_component_clause,[],[f37])).
% 16.56/2.44  fof(f5554,plain,(
% 16.56/2.44    spl5_32 | ~spl5_28),
% 16.56/2.44    inference(avatar_split_clause,[],[f3955,f3857,f5551])).
% 16.56/2.44  fof(f5551,plain,(
% 16.56/2.44    spl5_32 <=> k3_xboole_0(sK2,sK2) = k3_xboole_0(k3_xboole_0(sK3,sK3),sK2)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 16.56/2.44  fof(f3857,plain,(
% 16.56/2.44    spl5_28 <=> r1_tarski(k3_xboole_0(sK2,sK2),k3_xboole_0(sK3,sK3))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 16.56/2.44  fof(f3955,plain,(
% 16.56/2.44    k3_xboole_0(sK2,sK2) = k3_xboole_0(k3_xboole_0(sK3,sK3),sK2) | ~spl5_28),
% 16.56/2.44    inference(resolution,[],[f3859,f721])).
% 16.56/2.44  fof(f3859,plain,(
% 16.56/2.44    r1_tarski(k3_xboole_0(sK2,sK2),k3_xboole_0(sK3,sK3)) | ~spl5_28),
% 16.56/2.44    inference(avatar_component_clause,[],[f3857])).
% 16.56/2.44  fof(f5549,plain,(
% 16.56/2.44    spl5_31 | ~spl5_28),
% 16.56/2.44    inference(avatar_split_clause,[],[f3954,f3857,f5546])).
% 16.56/2.44  fof(f5546,plain,(
% 16.56/2.44    spl5_31 <=> k3_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK3,sK3))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 16.56/2.44  fof(f3954,plain,(
% 16.56/2.44    k3_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK3,sK3)) | ~spl5_28),
% 16.56/2.44    inference(resolution,[],[f3859,f734])).
% 16.56/2.44  fof(f734,plain,(
% 16.56/2.44    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(X0,X0),X1) | k3_xboole_0(X0,X1) = k3_xboole_0(X0,X0)) )),
% 16.56/2.44    inference(subsumption_resolution,[],[f733,f28])).
% 16.56/2.44  fof(f733,plain,(
% 16.56/2.44    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(X0,X0),X0) | k3_xboole_0(X0,X1) = k3_xboole_0(X0,X0) | ~r1_tarski(k3_xboole_0(X0,X0),X1)) )),
% 16.56/2.44    inference(duplicate_literal_removal,[],[f722])).
% 16.56/2.44  fof(f722,plain,(
% 16.56/2.44    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(X0,X0),X0) | k3_xboole_0(X0,X1) = k3_xboole_0(X0,X0) | ~r1_tarski(k3_xboole_0(X0,X0),X1) | k3_xboole_0(X0,X1) = k3_xboole_0(X0,X0) | ~r1_tarski(k3_xboole_0(X0,X0),X1) | ~r1_tarski(k3_xboole_0(X0,X0),X0)) )),
% 16.56/2.44    inference(resolution,[],[f160,f33])).
% 16.56/2.44  fof(f33,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (r1_tarski(sK4(X0,X1,X2),X1) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 16.56/2.44    inference(cnf_transformation,[],[f23])).
% 16.56/2.44  fof(f160,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (~r1_tarski(sK4(k3_xboole_0(X0,X1),X1,X2),X0) | ~r1_tarski(k3_xboole_0(X0,X1),X1) | k3_xboole_0(X0,X1) = k3_xboole_0(X1,X2) | ~r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 16.56/2.44    inference(duplicate_literal_removal,[],[f151])).
% 16.56/2.44  fof(f151,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (~r1_tarski(k3_xboole_0(X0,X1),X2) | ~r1_tarski(k3_xboole_0(X0,X1),X1) | k3_xboole_0(X0,X1) = k3_xboole_0(X1,X2) | ~r1_tarski(sK4(k3_xboole_0(X0,X1),X1,X2),X0) | k3_xboole_0(X0,X1) = k3_xboole_0(X1,X2) | ~r1_tarski(k3_xboole_0(X0,X1),X2) | ~r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 16.56/2.44    inference(resolution,[],[f71,f33])).
% 16.56/2.44  fof(f5544,plain,(
% 16.56/2.44    spl5_30 | ~spl5_27),
% 16.56/2.44    inference(avatar_split_clause,[],[f3521,f3439,f5541])).
% 16.56/2.44  fof(f5541,plain,(
% 16.56/2.44    spl5_30 <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(k3_xboole_0(sK1,sK1),sK0)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 16.56/2.44  fof(f3439,plain,(
% 16.56/2.44    spl5_27 <=> r1_tarski(k3_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK1))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 16.56/2.44  fof(f3521,plain,(
% 16.56/2.44    k3_xboole_0(sK0,sK0) = k3_xboole_0(k3_xboole_0(sK1,sK1),sK0) | ~spl5_27),
% 16.56/2.44    inference(resolution,[],[f3441,f721])).
% 16.56/2.44  fof(f3441,plain,(
% 16.56/2.44    r1_tarski(k3_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK1)) | ~spl5_27),
% 16.56/2.44    inference(avatar_component_clause,[],[f3439])).
% 16.56/2.44  fof(f5421,plain,(
% 16.56/2.44    spl5_29 | ~spl5_27),
% 16.56/2.44    inference(avatar_split_clause,[],[f3520,f3439,f5418])).
% 16.56/2.44  fof(f5418,plain,(
% 16.56/2.44    spl5_29 <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 16.56/2.44  fof(f3520,plain,(
% 16.56/2.44    k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK1)) | ~spl5_27),
% 16.56/2.44    inference(resolution,[],[f3441,f734])).
% 16.56/2.44  fof(f3860,plain,(
% 16.56/2.44    spl5_28 | ~spl5_2 | ~spl5_26),
% 16.56/2.44    inference(avatar_split_clause,[],[f3791,f3158,f42,f3857])).
% 16.56/2.44  fof(f3158,plain,(
% 16.56/2.44    spl5_26 <=> k3_xboole_0(sK2,sK2) = k3_xboole_0(k3_xboole_0(sK2,sK2),sK3)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 16.56/2.44  fof(f3791,plain,(
% 16.56/2.44    r1_tarski(k3_xboole_0(sK2,sK2),k3_xboole_0(sK3,sK3)) | (~spl5_2 | ~spl5_26)),
% 16.56/2.44    inference(superposition,[],[f999,f3160])).
% 16.56/2.44  fof(f3160,plain,(
% 16.56/2.44    k3_xboole_0(sK2,sK2) = k3_xboole_0(k3_xboole_0(sK2,sK2),sK3) | ~spl5_26),
% 16.56/2.44    inference(avatar_component_clause,[],[f3158])).
% 16.56/2.44  fof(f999,plain,(
% 16.56/2.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k3_xboole_0(sK2,X0),X1),k3_xboole_0(sK3,X1))) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f275,f28])).
% 16.56/2.44  fof(f275,plain,(
% 16.56/2.44    ( ! [X70,X71] : (~r1_tarski(X70,sK2) | r1_tarski(k3_xboole_0(X70,X71),k3_xboole_0(sK3,X71))) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f119,f44])).
% 16.56/2.44  fof(f3442,plain,(
% 16.56/2.44    spl5_27 | ~spl5_1 | ~spl5_25),
% 16.56/2.44    inference(avatar_split_clause,[],[f3299,f3146,f37,f3439])).
% 16.56/2.44  fof(f3146,plain,(
% 16.56/2.44    spl5_25 <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(k3_xboole_0(sK0,sK0),sK1)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 16.56/2.44  fof(f3299,plain,(
% 16.56/2.44    r1_tarski(k3_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK1)) | (~spl5_1 | ~spl5_25)),
% 16.56/2.44    inference(superposition,[],[f975,f3148])).
% 16.56/2.44  fof(f3148,plain,(
% 16.56/2.44    k3_xboole_0(sK0,sK0) = k3_xboole_0(k3_xboole_0(sK0,sK0),sK1) | ~spl5_25),
% 16.56/2.44    inference(avatar_component_clause,[],[f3146])).
% 16.56/2.44  fof(f975,plain,(
% 16.56/2.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X0),X1),k3_xboole_0(sK1,X1))) ) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f270,f28])).
% 16.56/2.44  fof(f270,plain,(
% 16.56/2.44    ( ! [X54,X53] : (~r1_tarski(X53,sK0) | r1_tarski(k3_xboole_0(X53,X54),k3_xboole_0(sK1,X54))) ) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f119,f39])).
% 16.56/2.44  fof(f3161,plain,(
% 16.56/2.44    spl5_26 | ~spl5_2),
% 16.56/2.44    inference(avatar_split_clause,[],[f3064,f42,f3158])).
% 16.56/2.44  fof(f3064,plain,(
% 16.56/2.44    k3_xboole_0(sK2,sK2) = k3_xboole_0(k3_xboole_0(sK2,sK2),sK3) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f559,f491])).
% 16.56/2.44  fof(f559,plain,(
% 16.56/2.44    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(X0,X0),X1) | k3_xboole_0(X0,X0) = k3_xboole_0(k3_xboole_0(X0,X0),X1)) )),
% 16.56/2.44    inference(resolution,[],[f116,f28])).
% 16.56/2.44  fof(f116,plain,(
% 16.56/2.44    ( ! [X4,X5,X3] : (~r1_tarski(k3_xboole_0(X3,X4),X4) | k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X5) | ~r1_tarski(k3_xboole_0(X3,X4),X5)) )),
% 16.56/2.44    inference(subsumption_resolution,[],[f113,f28])).
% 16.56/2.44  fof(f113,plain,(
% 16.56/2.44    ( ! [X4,X5,X3] : (~r1_tarski(k3_xboole_0(X3,X4),X5) | k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X5) | ~r1_tarski(k3_xboole_0(X3,X4),X4) | ~r1_tarski(k3_xboole_0(X3,X4),X3)) )),
% 16.56/2.44    inference(resolution,[],[f73,f32])).
% 16.56/2.44  fof(f73,plain,(
% 16.56/2.44    ( ! [X0,X1] : (~r1_tarski(X0,X0) | ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 16.56/2.44    inference(duplicate_literal_removal,[],[f68])).
% 16.56/2.44  fof(f68,plain,(
% 16.56/2.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0) | k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0)) )),
% 16.56/2.44    inference(resolution,[],[f35,f33])).
% 16.56/2.44  fof(f3149,plain,(
% 16.56/2.44    spl5_25 | ~spl5_1),
% 16.56/2.44    inference(avatar_split_clause,[],[f3059,f37,f3146])).
% 16.56/2.44  fof(f3059,plain,(
% 16.56/2.44    k3_xboole_0(sK0,sK0) = k3_xboole_0(k3_xboole_0(sK0,sK0),sK1) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f559,f850])).
% 16.56/2.44  fof(f850,plain,(
% 16.56/2.44    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),sK1)) ) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f810,f28])).
% 16.56/2.44  fof(f810,plain,(
% 16.56/2.44    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,sK1)) ) | ~spl5_1),
% 16.56/2.44    inference(condensation,[],[f798])).
% 16.56/2.44  fof(f798,plain,(
% 16.56/2.44    ( ! [X0,X1] : (r1_tarski(X0,sK1) | ~r1_tarski(X0,X1) | ~r1_tarski(X0,sK0)) ) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f786,f32])).
% 16.56/2.44  fof(f786,plain,(
% 16.56/2.44    ( ! [X0,X1] : (~r1_tarski(X0,k3_xboole_0(sK0,X1)) | r1_tarski(X0,sK1)) ) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f308,f28])).
% 16.56/2.44  fof(f308,plain,(
% 16.56/2.44    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | ~r1_tarski(X0,X1) | r1_tarski(X0,sK1)) ) | ~spl5_1),
% 16.56/2.44    inference(condensation,[],[f303])).
% 16.56/2.44  fof(f303,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,sK0) | ~r1_tarski(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,sK1)) ) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f229,f60])).
% 16.56/2.44  fof(f229,plain,(
% 16.56/2.44    ( ! [X47,X48] : (r1_tarski(k3_xboole_0(X47,X48),sK1) | ~r1_tarski(X47,sK0)) ) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f79,f39])).
% 16.56/2.44  fof(f3094,plain,(
% 16.56/2.44    spl5_24 | ~spl5_2),
% 16.56/2.44    inference(avatar_split_clause,[],[f3005,f42,f3091])).
% 16.56/2.44  fof(f3091,plain,(
% 16.56/2.44    spl5_24 <=> k3_xboole_0(sK2,sK2) = k3_xboole_0(sK3,k3_xboole_0(sK2,sK2))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 16.56/2.44  fof(f3005,plain,(
% 16.56/2.44    k3_xboole_0(sK2,sK2) = k3_xboole_0(sK3,k3_xboole_0(sK2,sK2)) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f520,f491])).
% 16.56/2.44  fof(f520,plain,(
% 16.56/2.44    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(X0,X0),X1) | k3_xboole_0(X0,X0) = k3_xboole_0(X1,k3_xboole_0(X0,X0))) )),
% 16.56/2.44    inference(resolution,[],[f111,f28])).
% 16.56/2.44  fof(f111,plain,(
% 16.56/2.44    ( ! [X4,X5,X3] : (~r1_tarski(k3_xboole_0(X4,X5),X5) | ~r1_tarski(k3_xboole_0(X4,X5),X3) | k3_xboole_0(X4,X5) = k3_xboole_0(X3,k3_xboole_0(X4,X5))) )),
% 16.56/2.44    inference(subsumption_resolution,[],[f108,f28])).
% 16.56/2.44  fof(f108,plain,(
% 16.56/2.44    ( ! [X4,X5,X3] : (k3_xboole_0(X4,X5) = k3_xboole_0(X3,k3_xboole_0(X4,X5)) | ~r1_tarski(k3_xboole_0(X4,X5),X3) | ~r1_tarski(k3_xboole_0(X4,X5),X5) | ~r1_tarski(k3_xboole_0(X4,X5),X4)) )),
% 16.56/2.44    inference(resolution,[],[f72,f32])).
% 16.56/2.44  fof(f72,plain,(
% 16.56/2.44    ( ! [X2,X3] : (~r1_tarski(X3,X3) | k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X2)) )),
% 16.56/2.44    inference(duplicate_literal_removal,[],[f69])).
% 16.56/2.44  fof(f69,plain,(
% 16.56/2.44    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2) | k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2)) )),
% 16.56/2.44    inference(resolution,[],[f35,f34])).
% 16.56/2.44  fof(f3035,plain,(
% 16.56/2.44    spl5_23 | ~spl5_1),
% 16.56/2.44    inference(avatar_split_clause,[],[f3000,f37,f3032])).
% 16.56/2.44  fof(f3032,plain,(
% 16.56/2.44    spl5_23 <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK0))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 16.56/2.44  fof(f3000,plain,(
% 16.56/2.44    k3_xboole_0(sK0,sK0) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK0)) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f520,f850])).
% 16.56/2.44  fof(f2196,plain,(
% 16.56/2.44    spl5_21 | ~spl5_22 | ~spl5_5),
% 16.56/2.44    inference(avatar_split_clause,[],[f355,f86,f2193,f2190])).
% 16.56/2.44  fof(f2190,plain,(
% 16.56/2.44    spl5_21 <=> ! [X46] : (~r1_tarski(sK1,X46) | sK1 = k3_xboole_0(k3_xboole_0(sK0,sK2),X46))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 16.56/2.44  fof(f2193,plain,(
% 16.56/2.44    spl5_22 <=> r1_tarski(sK1,k3_xboole_0(sK0,sK2))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 16.56/2.44  fof(f86,plain,(
% 16.56/2.44    spl5_5 <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 16.56/2.44  fof(f355,plain,(
% 16.56/2.44    ( ! [X46] : (~r1_tarski(sK1,k3_xboole_0(sK0,sK2)) | ~r1_tarski(sK1,X46) | sK1 = k3_xboole_0(k3_xboole_0(sK0,sK2),X46)) ) | ~spl5_5),
% 16.56/2.44    inference(resolution,[],[f138,f87])).
% 16.56/2.44  fof(f87,plain,(
% 16.56/2.44    r1_tarski(k3_xboole_0(sK0,sK2),sK1) | ~spl5_5),
% 16.56/2.44    inference(avatar_component_clause,[],[f86])).
% 16.56/2.44  fof(f138,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k3_xboole_0(X2,X1) = X0) )),
% 16.56/2.44    inference(duplicate_literal_removal,[],[f134])).
% 16.56/2.44  fof(f134,plain,(
% 16.56/2.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X2,X0) | k3_xboole_0(X2,X1) = X0 | k3_xboole_0(X2,X1) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X2)) )),
% 16.56/2.44    inference(resolution,[],[f63,f35])).
% 16.56/2.44  fof(f63,plain,(
% 16.56/2.44    ( ! [X2,X0,X3,X1] : (r1_tarski(sK4(X2,X0,X1),X3) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | ~r1_tarski(X0,X3) | k3_xboole_0(X0,X1) = X2) )),
% 16.56/2.44    inference(resolution,[],[f33,f31])).
% 16.56/2.44  fof(f2188,plain,(
% 16.56/2.44    spl5_20 | ~spl5_2),
% 16.56/2.44    inference(avatar_split_clause,[],[f1985,f42,f2185])).
% 16.56/2.44  fof(f2185,plain,(
% 16.56/2.44    spl5_20 <=> k3_xboole_0(sK2,sK2) = k3_xboole_0(sK2,sK3)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 16.56/2.44  fof(f1985,plain,(
% 16.56/2.44    k3_xboole_0(sK2,sK2) = k3_xboole_0(sK2,sK3) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f734,f491])).
% 16.56/2.44  fof(f2168,plain,(
% 16.56/2.44    spl5_19 | ~spl5_1),
% 16.56/2.44    inference(avatar_split_clause,[],[f1981,f37,f2165])).
% 16.56/2.44  fof(f2165,plain,(
% 16.56/2.44    spl5_19 <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,sK1)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 16.56/2.44  fof(f1981,plain,(
% 16.56/2.44    k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,sK1) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f734,f850])).
% 16.56/2.44  fof(f2070,plain,(
% 16.56/2.44    spl5_18 | ~spl5_2),
% 16.56/2.44    inference(avatar_split_clause,[],[f1941,f42,f2067])).
% 16.56/2.44  fof(f2067,plain,(
% 16.56/2.44    spl5_18 <=> k3_xboole_0(sK3,sK2) = k3_xboole_0(sK2,sK2)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 16.56/2.44  fof(f1941,plain,(
% 16.56/2.44    k3_xboole_0(sK3,sK2) = k3_xboole_0(sK2,sK2) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f721,f491])).
% 16.56/2.44  fof(f1962,plain,(
% 16.56/2.44    spl5_17 | ~spl5_1),
% 16.56/2.44    inference(avatar_split_clause,[],[f1937,f37,f1959])).
% 16.56/2.44  fof(f1959,plain,(
% 16.56/2.44    spl5_17 <=> k3_xboole_0(sK1,sK0) = k3_xboole_0(sK0,sK0)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 16.56/2.44  fof(f1937,plain,(
% 16.56/2.44    k3_xboole_0(sK1,sK0) = k3_xboole_0(sK0,sK0) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f721,f850])).
% 16.56/2.44  fof(f1206,plain,(
% 16.56/2.44    spl5_15 | ~spl5_16 | ~spl5_2),
% 16.56/2.44    inference(avatar_split_clause,[],[f362,f42,f1203,f1200])).
% 16.56/2.44  fof(f1200,plain,(
% 16.56/2.44    spl5_15 <=> ! [X61] : (~r1_tarski(sK3,X61) | sK3 = k3_xboole_0(sK2,X61))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 16.56/2.44  fof(f1203,plain,(
% 16.56/2.44    spl5_16 <=> r1_tarski(sK3,sK2)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 16.56/2.44  fof(f362,plain,(
% 16.56/2.44    ( ! [X61] : (~r1_tarski(sK3,sK2) | ~r1_tarski(sK3,X61) | sK3 = k3_xboole_0(sK2,X61)) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f138,f44])).
% 16.56/2.44  fof(f1198,plain,(
% 16.56/2.44    spl5_13 | ~spl5_14 | ~spl5_1),
% 16.56/2.44    inference(avatar_split_clause,[],[f357,f37,f1195,f1192])).
% 16.56/2.44  fof(f1192,plain,(
% 16.56/2.44    spl5_13 <=> ! [X49] : (~r1_tarski(sK1,X49) | sK1 = k3_xboole_0(sK0,X49))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 16.56/2.44  fof(f1195,plain,(
% 16.56/2.44    spl5_14 <=> r1_tarski(sK1,sK0)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 16.56/2.44  fof(f357,plain,(
% 16.56/2.44    ( ! [X49] : (~r1_tarski(sK1,sK0) | ~r1_tarski(sK1,X49) | sK1 = k3_xboole_0(sK0,X49)) ) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f138,f39])).
% 16.56/2.44  fof(f825,plain,(
% 16.56/2.44    spl5_11 | ~spl5_12 | ~spl5_1 | ~spl5_2),
% 16.56/2.44    inference(avatar_split_clause,[],[f808,f42,f37,f822,f818])).
% 16.56/2.44  fof(f818,plain,(
% 16.56/2.44    spl5_11 <=> r1_tarski(sK2,sK1)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 16.56/2.44  fof(f822,plain,(
% 16.56/2.44    spl5_12 <=> r1_tarski(sK3,sK0)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 16.56/2.44  fof(f808,plain,(
% 16.56/2.44    ~r1_tarski(sK3,sK0) | r1_tarski(sK2,sK1) | (~spl5_1 | ~spl5_2)),
% 16.56/2.44    inference(condensation,[],[f803])).
% 16.56/2.44  fof(f803,plain,(
% 16.56/2.44    ( ! [X10] : (r1_tarski(sK2,sK1) | ~r1_tarski(sK3,X10) | ~r1_tarski(sK3,sK0)) ) | (~spl5_1 | ~spl5_2)),
% 16.56/2.44    inference(resolution,[],[f786,f67])).
% 16.56/2.44  fof(f67,plain,(
% 16.56/2.44    ( ! [X4,X3] : (r1_tarski(sK2,k3_xboole_0(X3,X4)) | ~r1_tarski(sK3,X4) | ~r1_tarski(sK3,X3)) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f55,f32])).
% 16.56/2.44  fof(f55,plain,(
% 16.56/2.44    ( ! [X11] : (~r1_tarski(sK3,X11) | r1_tarski(sK2,X11)) ) | ~spl5_2),
% 16.56/2.44    inference(resolution,[],[f31,f44])).
% 16.56/2.44  fof(f466,plain,(
% 16.56/2.44    ~spl5_10 | ~spl5_1 | ~spl5_2 | spl5_7),
% 16.56/2.44    inference(avatar_split_clause,[],[f427,f100,f42,f37,f463])).
% 16.56/2.44  fof(f463,plain,(
% 16.56/2.44    spl5_10 <=> r1_tarski(sK1,sK2)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 16.56/2.44  fof(f100,plain,(
% 16.56/2.44    spl5_7 <=> r1_tarski(sK0,sK3)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 16.56/2.44  fof(f427,plain,(
% 16.56/2.44    ~r1_tarski(sK1,sK2) | (~spl5_1 | ~spl5_2 | spl5_7)),
% 16.56/2.44    inference(subsumption_resolution,[],[f425,f102])).
% 16.56/2.44  fof(f102,plain,(
% 16.56/2.44    ~r1_tarski(sK0,sK3) | spl5_7),
% 16.56/2.44    inference(avatar_component_clause,[],[f100])).
% 16.56/2.44  fof(f425,plain,(
% 16.56/2.44    ~r1_tarski(sK1,sK2) | r1_tarski(sK0,sK3) | (~spl5_1 | ~spl5_2)),
% 16.56/2.44    inference(condensation,[],[f418])).
% 16.56/2.44  fof(f418,plain,(
% 16.56/2.44    ( ! [X9] : (r1_tarski(sK0,sK3) | ~r1_tarski(sK1,sK2) | ~r1_tarski(sK1,X9)) ) | (~spl5_1 | ~spl5_2)),
% 16.56/2.44    inference(resolution,[],[f407,f61])).
% 16.56/2.44  fof(f61,plain,(
% 16.56/2.44    ( ! [X4,X5] : (r1_tarski(sK0,k3_xboole_0(X5,X4)) | ~r1_tarski(sK1,X5) | ~r1_tarski(sK1,X4)) ) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f32,f54])).
% 16.56/2.44  fof(f54,plain,(
% 16.56/2.44    ( ! [X10] : (~r1_tarski(sK1,X10) | r1_tarski(sK0,X10)) ) | ~spl5_1),
% 16.56/2.44    inference(resolution,[],[f31,f39])).
% 16.56/2.44  fof(f197,plain,(
% 16.56/2.44    ~spl5_8 | ~spl5_9 | ~spl5_1 | spl5_4),
% 16.56/2.44    inference(avatar_split_clause,[],[f187,f81,f37,f194,f190])).
% 16.56/2.44  fof(f190,plain,(
% 16.56/2.44    spl5_8 <=> r1_tarski(sK1,sK3)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 16.56/2.44  fof(f194,plain,(
% 16.56/2.44    spl5_9 <=> r1_tarski(sK1,sK1)),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 16.56/2.44  fof(f81,plain,(
% 16.56/2.44    spl5_4 <=> r1_tarski(sK0,k3_xboole_0(sK1,sK3))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 16.56/2.44  fof(f187,plain,(
% 16.56/2.44    ~r1_tarski(sK1,sK1) | ~r1_tarski(sK1,sK3) | (~spl5_1 | spl5_4)),
% 16.56/2.44    inference(resolution,[],[f61,f83])).
% 16.56/2.44  fof(f83,plain,(
% 16.56/2.44    ~r1_tarski(sK0,k3_xboole_0(sK1,sK3)) | spl5_4),
% 16.56/2.44    inference(avatar_component_clause,[],[f81])).
% 16.56/2.44  fof(f103,plain,(
% 16.56/2.44    ~spl5_7 | spl5_6),
% 16.56/2.44    inference(avatar_split_clause,[],[f98,f90,f100])).
% 16.56/2.44  fof(f98,plain,(
% 16.56/2.44    ~r1_tarski(sK0,sK3) | spl5_6),
% 16.56/2.44    inference(resolution,[],[f92,f53])).
% 16.56/2.44  fof(f96,plain,(
% 16.56/2.44    ~spl5_1 | spl5_5),
% 16.56/2.44    inference(avatar_contradiction_clause,[],[f95])).
% 16.56/2.44  fof(f95,plain,(
% 16.56/2.44    $false | (~spl5_1 | spl5_5)),
% 16.56/2.44    inference(subsumption_resolution,[],[f94,f39])).
% 16.56/2.44  fof(f94,plain,(
% 16.56/2.44    ~r1_tarski(sK0,sK1) | spl5_5),
% 16.56/2.44    inference(resolution,[],[f88,f53])).
% 16.56/2.44  fof(f88,plain,(
% 16.56/2.44    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | spl5_5),
% 16.56/2.44    inference(avatar_component_clause,[],[f86])).
% 16.56/2.44  fof(f93,plain,(
% 16.56/2.44    ~spl5_5 | ~spl5_6 | spl5_3),
% 16.56/2.44    inference(avatar_split_clause,[],[f59,f47,f90,f86])).
% 16.56/2.44  fof(f47,plain,(
% 16.56/2.44    spl5_3 <=> r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 16.56/2.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 16.56/2.44  fof(f59,plain,(
% 16.56/2.44    ~r1_tarski(k3_xboole_0(sK0,sK2),sK3) | ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | spl5_3),
% 16.56/2.44    inference(resolution,[],[f32,f49])).
% 16.56/2.44  fof(f49,plain,(
% 16.56/2.44    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) | spl5_3),
% 16.56/2.44    inference(avatar_component_clause,[],[f47])).
% 16.56/2.44  fof(f84,plain,(
% 16.56/2.44    ~spl5_4 | spl5_3),
% 16.56/2.44    inference(avatar_split_clause,[],[f78,f47,f81])).
% 16.56/2.44  fof(f78,plain,(
% 16.56/2.44    ~r1_tarski(sK0,k3_xboole_0(sK1,sK3)) | spl5_3),
% 16.56/2.44    inference(resolution,[],[f53,f49])).
% 16.56/2.44  fof(f50,plain,(
% 16.56/2.44    ~spl5_3),
% 16.56/2.44    inference(avatar_split_clause,[],[f26,f47])).
% 16.56/2.44  fof(f26,plain,(
% 16.56/2.44    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 16.56/2.44    inference(cnf_transformation,[],[f21])).
% 16.56/2.44  fof(f21,plain,(
% 16.56/2.44    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 16.56/2.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20])).
% 16.56/2.44  fof(f20,plain,(
% 16.56/2.44    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 16.56/2.44    introduced(choice_axiom,[])).
% 16.56/2.44  fof(f11,plain,(
% 16.56/2.44    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 16.56/2.44    inference(flattening,[],[f10])).
% 16.56/2.44  fof(f10,plain,(
% 16.56/2.44    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 16.56/2.44    inference(ennf_transformation,[],[f9])).
% 16.56/2.44  fof(f9,negated_conjecture,(
% 16.56/2.44    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 16.56/2.44    inference(negated_conjecture,[],[f8])).
% 16.56/2.44  fof(f8,conjecture,(
% 16.56/2.44    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 16.56/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).
% 16.56/2.44  fof(f45,plain,(
% 16.56/2.44    spl5_2),
% 16.56/2.44    inference(avatar_split_clause,[],[f25,f42])).
% 16.56/2.44  fof(f25,plain,(
% 16.56/2.44    r1_tarski(sK2,sK3)),
% 16.56/2.44    inference(cnf_transformation,[],[f21])).
% 16.56/2.44  fof(f40,plain,(
% 16.56/2.44    spl5_1),
% 16.56/2.44    inference(avatar_split_clause,[],[f24,f37])).
% 16.56/2.44  fof(f24,plain,(
% 16.56/2.44    r1_tarski(sK0,sK1)),
% 16.56/2.44    inference(cnf_transformation,[],[f21])).
% 16.56/2.44  % SZS output end Proof for theBenchmark
% 16.56/2.44  % (21840)------------------------------
% 16.56/2.44  % (21840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.56/2.44  % (21840)Termination reason: Refutation
% 16.56/2.44  
% 16.56/2.44  % (21840)Memory used [KB]: 26353
% 16.56/2.44  % (21840)Time elapsed: 1.986 s
% 16.56/2.44  % (21840)------------------------------
% 16.56/2.44  % (21840)------------------------------
% 16.56/2.45  % (21833)Success in time 2.087 s
%------------------------------------------------------------------------------
