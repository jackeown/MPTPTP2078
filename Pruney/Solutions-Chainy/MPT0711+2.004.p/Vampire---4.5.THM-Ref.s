%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 448 expanded)
%              Number of leaves         :   27 ( 172 expanded)
%              Depth                    :   14
%              Number of atoms          :  499 (1752 expanded)
%              Number of equality atoms :  128 ( 667 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1915,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f92,f199,f350,f609,f1081,f1548,f1870,f1914])).

fof(f1914,plain,
    ( ~ spl5_6
    | spl5_59 ),
    inference(avatar_contradiction_clause,[],[f1909])).

fof(f1909,plain,
    ( $false
    | ~ spl5_6
    | spl5_59 ),
    inference(unit_resulting_resolution,[],[f91,f1869,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f1869,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | spl5_59 ),
    inference(avatar_component_clause,[],[f1867])).

fof(f1867,plain,
    ( spl5_59
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f91,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1870,plain,
    ( ~ spl5_4
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_5
    | spl5_1
    | ~ spl5_59
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1865,f1218,f89,f79,f69,f1867,f64,f84,f89,f74,f79])).

fof(f74,plain,
    ( spl5_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f84,plain,
    ( spl5_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f64,plain,
    ( spl5_1
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f69,plain,
    ( spl5_2
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f79,plain,
    ( spl5_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1218,plain,
    ( spl5_38
  <=> k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f1865,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(duplicate_literal_removal,[],[f1864])).

fof(f1864,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(forward_demodulation,[],[f1863,f71])).

fof(f71,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f1863,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(forward_demodulation,[],[f1862,f383])).

fof(f383,plain,
    ( ! [X1] : k7_relat_1(sK0,X1) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X1)))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f376,f139])).

fof(f139,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK0)))
    | ~ spl5_6 ),
    inference(superposition,[],[f121,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f51,f60,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f121,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X0))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f91,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f376,plain,
    ( ! [X1] : k7_relat_1(sK0,X1) = k7_relat_1(sK0,k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK0))))
    | ~ spl5_6 ),
    inference(superposition,[],[f157,f126])).

fof(f126,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK4(X0),X1)) ),
    inference(forward_demodulation,[],[f122,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = k1_xboole_0
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k1_xboole_0
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = k1_xboole_0 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

fof(f122,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(sK4(X0),X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK4(X0)),k1_relat_1(sK4(X0)),X1)) ),
    inference(unit_resulting_resolution,[],[f47,f62])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f157,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0))))
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f150,f49])).

fof(f150,plain,
    ( ! [X0] : k7_relat_1(sK0,k1_relat_1(sK4(X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0))))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f91,f47,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(f1862,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(forward_demodulation,[],[f1861,f418])).

fof(f418,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f159,f368])).

fof(f368,plain,
    ( ! [X6] : k1_relat_1(k7_relat_1(sK0,X6)) = k1_relat_1(k7_relat_1(sK4(X6),k1_relat_1(sK0)))
    | ~ spl5_6 ),
    inference(superposition,[],[f126,f139])).

fof(f159,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0))))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f158,f49])).

fof(f158,plain,
    ( ! [X0] : k7_relat_1(sK1,k1_relat_1(sK4(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0))))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f149,f71])).

fof(f149,plain,
    ( ! [X0] : k7_relat_1(sK1,k1_relat_1(sK4(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK1))))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f81,f47,f43])).

fof(f81,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f1861,plain,
    ( k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_38 ),
    inference(trivial_inequality_removal,[],[f1860])).

fof(f1860,plain,
    ( k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))
    | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_38 ),
    inference(superposition,[],[f46,f1220])).

fof(f1220,plain,
    ( k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f1218])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

fof(f1548,plain,
    ( spl5_38
    | spl5_1
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f1538,f1079,f64,f1218])).

fof(f1079,plain,
    ( spl5_33
  <=> ! [X3] :
        ( k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f1538,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))
    | ~ spl5_33 ),
    inference(resolution,[],[f1080,f41])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).

fof(f1080,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3)
        | k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f1079])).

fof(f1081,plain,
    ( ~ spl5_6
    | spl5_33
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f1063,f607,f1079,f89])).

fof(f607,plain,
    ( spl5_26
  <=> ! [X0] :
        ( k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f1063,plain,
    ( ! [X3] :
        ( k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3)
        | ~ v1_relat_1(sK0) )
    | ~ spl5_26 ),
    inference(resolution,[],[f608,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f608,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
        | k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f607])).

fof(f609,plain,
    ( ~ spl5_6
    | spl5_26
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f605,f348,f89,f79,f69,f607,f89])).

fof(f348,plain,
    ( spl5_22
  <=> ! [X1] :
        ( k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)
        | r2_hidden(sK3(sK1,sK0,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f605,plain,
    ( ! [X0] :
        ( k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f604,f383])).

fof(f604,plain,
    ( ! [X0] :
        ( k7_relat_1(sK1,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f598,f418])).

fof(f598,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0)))
        | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))
        | ~ v1_relat_1(sK0) )
    | ~ spl5_22 ),
    inference(resolution,[],[f349,f54])).

fof(f349,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK1,sK0,X1),X1)
        | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f348])).

fof(f350,plain,
    ( ~ spl5_6
    | spl5_22
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f346,f197,f84,f348,f89])).

fof(f197,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | r2_hidden(sK3(sK1,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f346,plain,
    ( ! [X1] :
        ( k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK1,sK0,X1),X1) )
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,
    ( ! [X1] :
        ( k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK1,sK0,X1),X1) )
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(resolution,[],[f198,f86])).

fof(f86,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | r2_hidden(sK3(sK1,X0,X1),X1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f197])).

fof(f199,plain,
    ( ~ spl5_4
    | spl5_14
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f195,f74,f69,f197,f79])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK1,X0,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f192,f71])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK1,X0,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | ~ r1_tarski(X1,k1_relat_1(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f45,f76])).

fof(f76,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f45,plain,(
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

fof(f92,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f36,f89])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f38,f79])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f40,f69])).

fof(f40,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f42,f64])).

fof(f42,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:10:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (24596)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.44  % (24588)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.45  % (24583)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (24586)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (24585)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (24590)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (24598)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (24595)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (24594)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (24587)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (24593)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (24584)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (24592)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (24597)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (24591)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (24582)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (24599)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (24589)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (24588)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f1915,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f92,f199,f350,f609,f1081,f1548,f1870,f1914])).
% 0.20/0.51  fof(f1914,plain,(
% 0.20/0.51    ~spl5_6 | spl5_59),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f1909])).
% 0.20/0.51  fof(f1909,plain,(
% 0.20/0.51    $false | (~spl5_6 | spl5_59)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f91,f1869,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 0.20/0.51  fof(f1869,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | spl5_59),
% 0.20/0.51    inference(avatar_component_clause,[],[f1867])).
% 0.20/0.51  fof(f1867,plain,(
% 0.20/0.51    spl5_59 <=> r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    v1_relat_1(sK0) | ~spl5_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl5_6 <=> v1_relat_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.51  fof(f1870,plain,(
% 0.20/0.51    ~spl5_4 | ~spl5_3 | ~spl5_6 | ~spl5_5 | spl5_1 | ~spl5_59 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_38),
% 0.20/0.51    inference(avatar_split_clause,[],[f1865,f1218,f89,f79,f69,f1867,f64,f84,f89,f74,f79])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    spl5_3 <=> v1_funct_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    spl5_5 <=> v1_funct_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl5_1 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl5_2 <=> k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl5_4 <=> v1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f1218,plain,(
% 0.20/0.51    spl5_38 <=> k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.20/0.51  fof(f1865,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_38)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f1864])).
% 0.20/0.51  fof(f1864,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_38)),
% 0.20/0.51    inference(forward_demodulation,[],[f1863,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k1_relat_1(sK1) | ~spl5_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f69])).
% 0.20/0.51  fof(f1863,plain,(
% 0.20/0.51    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_38)),
% 0.20/0.51    inference(forward_demodulation,[],[f1862,f383])).
% 0.20/0.51  fof(f383,plain,(
% 0.20/0.51    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X1)))) ) | ~spl5_6),
% 0.20/0.51    inference(forward_demodulation,[],[f376,f139])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    ( ! [X1] : (k1_relat_1(k7_relat_1(sK0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK0)))) ) | ~spl5_6),
% 0.20/0.51    inference(superposition,[],[f121,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f51,f60,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f52,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),X0))) ) | ~spl5_6),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f91,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f55,f60])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.51  fof(f376,plain,(
% 0.20/0.51    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK0,k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK0))))) ) | ~spl5_6),
% 0.20/0.51    inference(superposition,[],[f157,f126])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK4(X0),X1))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f122,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = k1_xboole_0 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = k1_xboole_0 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = k1_xboole_0) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(sK4(X0),X1)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK4(X0)),k1_relat_1(sK4(X0)),X1))) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f47,f62])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0))))) ) | ~spl5_6),
% 0.20/0.51    inference(forward_demodulation,[],[f150,f49])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK0,k1_relat_1(sK4(X0))) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0))))) ) | ~spl5_6),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f91,f47,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).
% 0.20/0.51  fof(f1862,plain,(
% 0.20/0.51    k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_38)),
% 0.20/0.51    inference(forward_demodulation,[],[f1861,f418])).
% 0.20/0.51  fof(f418,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))) ) | (~spl5_2 | ~spl5_4 | ~spl5_6)),
% 0.20/0.51    inference(backward_demodulation,[],[f159,f368])).
% 0.20/0.51  fof(f368,plain,(
% 0.20/0.51    ( ! [X6] : (k1_relat_1(k7_relat_1(sK0,X6)) = k1_relat_1(k7_relat_1(sK4(X6),k1_relat_1(sK0)))) ) | ~spl5_6),
% 0.20/0.51    inference(superposition,[],[f126,f139])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0))))) ) | (~spl5_2 | ~spl5_4)),
% 0.20/0.51    inference(forward_demodulation,[],[f158,f49])).
% 0.20/0.51  fof(f158,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK1,k1_relat_1(sK4(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK0))))) ) | (~spl5_2 | ~spl5_4)),
% 0.20/0.51    inference(forward_demodulation,[],[f149,f71])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK1,k1_relat_1(sK4(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK4(X0),k1_relat_1(sK1))))) ) | ~spl5_4),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f81,f47,f43])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    v1_relat_1(sK1) | ~spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f79])).
% 0.20/0.51  fof(f1861,plain,(
% 0.20/0.51    k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl5_38),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f1860])).
% 0.20/0.51  fof(f1860,plain,(
% 0.20/0.51    k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl5_38),
% 0.20/0.51    inference(superposition,[],[f46,f1220])).
% 0.20/0.51  fof(f1220,plain,(
% 0.20/0.51    k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) | ~spl5_38),
% 0.20/0.51    inference(avatar_component_clause,[],[f1218])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(rectify,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).
% 0.20/0.51  fof(f1548,plain,(
% 0.20/0.51    spl5_38 | spl5_1 | ~spl5_33),
% 0.20/0.51    inference(avatar_split_clause,[],[f1538,f1079,f64,f1218])).
% 0.20/0.51  fof(f1079,plain,(
% 0.20/0.51    spl5_33 <=> ! [X3] : (k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.20/0.51  fof(f1538,plain,(
% 0.20/0.51    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) | ~spl5_33),
% 0.20/0.51    inference(resolution,[],[f1080,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.20/0.51    inference(negated_conjecture,[],[f11])).
% 0.20/0.51  fof(f11,conjecture,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).
% 0.20/0.51  fof(f1080,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3) | k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)) ) | ~spl5_33),
% 0.20/0.51    inference(avatar_component_clause,[],[f1079])).
% 0.20/0.51  fof(f1081,plain,(
% 0.20/0.51    ~spl5_6 | spl5_33 | ~spl5_26),
% 0.20/0.51    inference(avatar_split_clause,[],[f1063,f607,f1079,f89])).
% 0.20/0.51  fof(f607,plain,(
% 0.20/0.51    spl5_26 <=> ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.20/0.51  fof(f1063,plain,(
% 0.20/0.51    ( ! [X3] : (k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3) | ~v1_relat_1(sK0)) ) | ~spl5_26),
% 0.20/0.51    inference(resolution,[],[f608,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.20/0.51  fof(f608,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0)) ) | ~spl5_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f607])).
% 0.20/0.51  fof(f609,plain,(
% 0.20/0.51    ~spl5_6 | spl5_26 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f605,f348,f89,f79,f69,f607,f89])).
% 0.20/0.51  fof(f348,plain,(
% 0.20/0.51    spl5_22 <=> ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) | r2_hidden(sK3(sK1,sK0,X1),X1) | ~r1_tarski(X1,k1_relat_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.51  fof(f605,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK0,X0) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_22)),
% 0.20/0.51    inference(forward_demodulation,[],[f604,f383])).
% 0.20/0.51  fof(f604,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) ) | (~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_22)),
% 0.20/0.51    inference(forward_demodulation,[],[f598,f418])).
% 0.20/0.51  fof(f598,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X0))),k1_relat_1(k7_relat_1(sK0,X0))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0))) | ~v1_relat_1(sK0)) ) | ~spl5_22),
% 0.20/0.51    inference(resolution,[],[f349,f54])).
% 0.20/0.51  fof(f349,plain,(
% 0.20/0.51    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,sK0,X1),X1) | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)) ) | ~spl5_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f348])).
% 0.20/0.51  fof(f350,plain,(
% 0.20/0.51    ~spl5_6 | spl5_22 | ~spl5_5 | ~spl5_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f346,f197,f84,f348,f89])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    spl5_14 <=> ! [X1,X0] : (~r1_tarski(X1,k1_relat_1(sK0)) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | r2_hidden(sK3(sK1,X0,X1),X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.51  fof(f346,plain,(
% 0.20/0.51    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK0) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,sK0,X1),X1)) ) | (~spl5_5 | ~spl5_14)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f344])).
% 0.20/0.51  fof(f344,plain,(
% 0.20/0.51    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK0) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,sK0,X1),X1)) ) | (~spl5_5 | ~spl5_14)),
% 0.20/0.51    inference(resolution,[],[f198,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    v1_funct_1(sK0) | ~spl5_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f84])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(X0) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~r1_tarski(X1,k1_relat_1(X0)) | r2_hidden(sK3(sK1,X0,X1),X1)) ) | ~spl5_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f197])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    ~spl5_4 | spl5_14 | ~spl5_2 | ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f195,f74,f69,f197,f79])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,X0,X1),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK1)) ) | (~spl5_2 | ~spl5_3)),
% 0.20/0.51    inference(forward_demodulation,[],[f192,f71])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK3(sK1,X0,X1),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | ~r1_tarski(X1,k1_relat_1(sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK1)) ) | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f45,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    v1_funct_1(sK1) | ~spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f74])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK3(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl5_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f36,f89])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    spl5_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f37,f84])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    v1_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f79])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    v1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f39,f74])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    v1_funct_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f40,f69])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ~spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f42,f64])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (24588)------------------------------
% 0.20/0.51  % (24588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24588)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (24588)Memory used [KB]: 7419
% 0.20/0.51  % (24588)Time elapsed: 0.074 s
% 0.20/0.51  % (24588)------------------------------
% 0.20/0.51  % (24588)------------------------------
% 0.20/0.52  % (24578)Success in time 0.167 s
%------------------------------------------------------------------------------
