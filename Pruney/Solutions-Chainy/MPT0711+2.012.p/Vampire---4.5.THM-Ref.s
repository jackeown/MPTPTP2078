%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 291 expanded)
%              Number of leaves         :   26 ( 123 expanded)
%              Depth                    :   14
%              Number of atoms          :  490 (1265 expanded)
%              Number of equality atoms :  116 ( 414 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f899,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f78,f95,f96,f135,f216,f305,f477,f636,f880,f898])).

fof(f898,plain,
    ( ~ spl4_6
    | spl4_40 ),
    inference(avatar_contradiction_clause,[],[f893])).

fof(f893,plain,
    ( $false
    | ~ spl4_6
    | spl4_40 ),
    inference(unit_resulting_resolution,[],[f77,f879,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(f879,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f877])).

fof(f877,plain,
    ( spl4_40
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f77,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f880,plain,
    ( ~ spl4_4
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_5
    | spl4_1
    | ~ spl4_40
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f875,f539,f90,f84,f75,f65,f55,f877,f50,f70,f75,f60,f65])).

fof(f60,plain,
    ( spl4_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f70,plain,
    ( spl4_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f50,plain,
    ( spl4_1
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f55,plain,
    ( spl4_2
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f84,plain,
    ( spl4_7
  <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f90,plain,
    ( spl4_8
  <=> sK1 = k7_relat_1(sK1,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f539,plain,
    ( spl4_36
  <=> k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f875,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(duplicate_literal_removal,[],[f874])).

fof(f874,plain,
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
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f873,f57])).

fof(f57,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f873,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f872,f195])).

fof(f195,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f188,f86])).

fof(f86,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f188,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl4_6 ),
    inference(superposition,[],[f125,f114])).

fof(f114,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f77,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f125,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f77,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f43,f40])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f872,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f871,f170])).

fof(f170,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f165,f92])).

fof(f92,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f165,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)),X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(superposition,[],[f124,f114])).

fof(f124,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f67,f48])).

fof(f67,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f871,plain,
    ( k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_36 ),
    inference(trivial_inequality_removal,[],[f870])).

fof(f870,plain,
    ( k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))
    | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_36 ),
    inference(superposition,[],[f39,f541])).

fof(f541,plain,
    ( k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f539])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,X2) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f636,plain,
    ( spl4_36
    | spl4_1
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f619,f475,f50,f539])).

fof(f475,plain,
    ( spl4_30
  <=> ! [X3] :
        ( k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f619,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))
    | ~ spl4_30 ),
    inference(resolution,[],[f476,f34])).

fof(f34,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & ! [X3] :
        ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK2) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).

fof(f19,plain,
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

fof(f20,plain,
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

fof(f21,plain,
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

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f476,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3)
        | k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f475])).

fof(f477,plain,
    ( ~ spl4_6
    | spl4_30
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f458,f303,f475,f75])).

fof(f303,plain,
    ( spl4_23
  <=> ! [X17] :
        ( k7_relat_1(sK0,X17) = k7_relat_1(sK1,X17)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X17))),k1_relat_1(k7_relat_1(sK0,X17))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f458,plain,
    ( ! [X3] :
        ( k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3)
        | ~ v1_relat_1(sK0) )
    | ~ spl4_23 ),
    inference(resolution,[],[f304,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f304,plain,
    ( ! [X17] :
        ( r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X17))),k1_relat_1(k7_relat_1(sK0,X17)))
        | k7_relat_1(sK0,X17) = k7_relat_1(sK1,X17) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f303])).

fof(f305,plain,
    ( ~ spl4_6
    | spl4_23
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f301,f214,f90,f84,f75,f65,f303,f75])).

fof(f214,plain,
    ( spl4_21
  <=> ! [X1] :
        ( k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)
        | r2_hidden(sK3(sK1,sK0,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f301,plain,
    ( ! [X17] :
        ( k7_relat_1(sK0,X17) = k7_relat_1(sK1,X17)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X17))),k1_relat_1(k7_relat_1(sK0,X17)))
        | ~ v1_relat_1(sK0) )
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f300,f195])).

fof(f300,plain,
    ( ! [X17] :
        ( k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X17))) = k7_relat_1(sK1,X17)
        | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X17))),k1_relat_1(k7_relat_1(sK0,X17)))
        | ~ v1_relat_1(sK0) )
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f296,f170])).

fof(f296,plain,
    ( ! [X17] :
        ( r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X17))),k1_relat_1(k7_relat_1(sK0,X17)))
        | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X17))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X17)))
        | ~ v1_relat_1(sK0) )
    | ~ spl4_21 ),
    inference(resolution,[],[f215,f41])).

fof(f215,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK1,sK0,X1),X1)
        | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( ~ spl4_6
    | spl4_21
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f212,f133,f70,f214,f75])).

fof(f133,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,k1_relat_1(sK0))
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | r2_hidden(sK3(sK1,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f212,plain,
    ( ! [X1] :
        ( k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK1,sK0,X1),X1) )
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,
    ( ! [X1] :
        ( k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | r2_hidden(sK3(sK1,sK0,X1),X1) )
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(resolution,[],[f134,f72])).

fof(f72,plain,
    ( v1_funct_1(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X1,k1_relat_1(sK0))
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | r2_hidden(sK3(sK1,X0,X1),X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( ~ spl4_4
    | spl4_11
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f131,f60,f55,f133,f65])).

fof(f131,plain,
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
    inference(forward_demodulation,[],[f129,f57])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK1,X0,X1),X1)
        | ~ r1_tarski(X1,k1_relat_1(X0))
        | ~ r1_tarski(X1,k1_relat_1(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f38,f62])).

fof(f62,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r1_tarski(X2,k1_relat_1(X1))
      | ~ r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f96,plain,
    ( spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f82,f75,f84])).

fof(f82,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl4_6 ),
    inference(resolution,[],[f36,f77])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f95,plain,
    ( spl4_8
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f94,f65,f55,f90])).

fof(f94,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK0))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f81,f57])).

fof(f81,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f36,f67])).

fof(f78,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f33,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f50])).

fof(f35,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (20999)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (20993)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (21003)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (21000)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (20989)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (20995)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (21004)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (20994)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (21006)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (21001)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (20990)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (20992)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (20996)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (21002)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (21005)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (20991)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (20997)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (20998)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (20995)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f899,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f78,f95,f96,f135,f216,f305,f477,f636,f880,f898])).
% 0.20/0.51  fof(f898,plain,(
% 0.20/0.51    ~spl4_6 | spl4_40),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f893])).
% 0.20/0.51  fof(f893,plain,(
% 0.20/0.51    $false | (~spl4_6 | spl4_40)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f77,f879,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).
% 0.20/0.51  fof(f879,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | spl4_40),
% 0.20/0.51    inference(avatar_component_clause,[],[f877])).
% 0.20/0.51  fof(f877,plain,(
% 0.20/0.51    spl4_40 <=> r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    v1_relat_1(sK0) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    spl4_6 <=> v1_relat_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f880,plain,(
% 0.20/0.51    ~spl4_4 | ~spl4_3 | ~spl4_6 | ~spl4_5 | spl4_1 | ~spl4_40 | ~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_36),
% 0.20/0.51    inference(avatar_split_clause,[],[f875,f539,f90,f84,f75,f65,f55,f877,f50,f70,f75,f60,f65])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    spl4_3 <=> v1_funct_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl4_5 <=> v1_funct_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl4_1 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    spl4_2 <=> k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    spl4_4 <=> v1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    spl4_7 <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl4_8 <=> sK1 = k7_relat_1(sK1,k1_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.51  fof(f539,plain,(
% 0.20/0.51    spl4_36 <=> k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.51  fof(f875,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_36)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f874])).
% 0.20/0.51  fof(f874,plain,(
% 0.20/0.51    ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_36)),
% 0.20/0.51    inference(forward_demodulation,[],[f873,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k1_relat_1(sK1) | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f55])).
% 0.20/0.51  fof(f873,plain,(
% 0.20/0.51    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_36)),
% 0.20/0.51    inference(forward_demodulation,[],[f872,f195])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) ) | (~spl4_6 | ~spl4_7)),
% 0.20/0.51    inference(forward_demodulation,[],[f188,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl4_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f84])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) ) | ~spl4_6),
% 0.20/0.51    inference(superposition,[],[f125,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))) ) | ~spl4_6),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f77,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f42,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl4_6),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f77,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f43,f40])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.51  fof(f872,plain,(
% 0.20/0.51    k7_relat_1(sK1,sK2) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_36)),
% 0.20/0.51    inference(forward_demodulation,[],[f871,f170])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))) ) | (~spl4_4 | ~spl4_6 | ~spl4_8)),
% 0.20/0.51    inference(forward_demodulation,[],[f165,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    sK1 = k7_relat_1(sK1,k1_relat_1(sK0)) | ~spl4_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f90])).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)),X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X0)))) ) | (~spl4_4 | ~spl4_6)),
% 0.20/0.51    inference(superposition,[],[f124,f114])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl4_4),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f67,f48])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    v1_relat_1(sK1) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f65])).
% 0.20/0.51  fof(f871,plain,(
% 0.20/0.51    k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_36),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f870])).
% 0.20/0.51  fof(f870,plain,(
% 0.20/0.51    k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) != k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,sK2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,sK2))) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_36),
% 0.20/0.51    inference(superposition,[],[f39,f541])).
% 0.20/0.51  fof(f541,plain,(
% 0.20/0.51    k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) | ~spl4_36),
% 0.20/0.51    inference(avatar_component_clause,[],[f539])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2)) => (k1_funct_1(X0,sK3(X0,X1,X2)) != k1_funct_1(X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X4] : (k1_funct_1(X0,X4) = k1_funct_1(X1,X4) | ~r2_hidden(X4,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(rectify,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ? [X3] : (k1_funct_1(X0,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,X2))) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) | k7_relat_1(X0,X2) != k7_relat_1(X1,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2))) | (~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).
% 0.20/0.51  fof(f636,plain,(
% 0.20/0.51    spl4_36 | spl4_1 | ~spl4_30),
% 0.20/0.51    inference(avatar_split_clause,[],[f619,f475,f50,f539])).
% 0.20/0.51  fof(f475,plain,(
% 0.20/0.51    spl4_30 <=> ! [X3] : (k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.51  fof(f619,plain,(
% 0.20/0.51    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | k1_funct_1(sK0,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,sK2)))) | ~spl4_30),
% 0.20/0.51    inference(resolution,[],[f476,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21,f20,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X0,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.20/0.51    inference(negated_conjecture,[],[f8])).
% 0.20/0.51  fof(f8,conjecture,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X0,X3) = k1_funct_1(X1,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).
% 0.20/0.51  fof(f476,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3) | k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3)) ) | ~spl4_30),
% 0.20/0.51    inference(avatar_component_clause,[],[f475])).
% 0.20/0.51  fof(f477,plain,(
% 0.20/0.51    ~spl4_6 | spl4_30 | ~spl4_23),
% 0.20/0.51    inference(avatar_split_clause,[],[f458,f303,f475,f75])).
% 0.20/0.51  fof(f303,plain,(
% 0.20/0.51    spl4_23 <=> ! [X17] : (k7_relat_1(sK0,X17) = k7_relat_1(sK1,X17) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X17))),k1_relat_1(k7_relat_1(sK0,X17))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.51  fof(f458,plain,(
% 0.20/0.51    ( ! [X3] : (k7_relat_1(sK0,X3) = k7_relat_1(sK1,X3) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X3))),X3) | ~v1_relat_1(sK0)) ) | ~spl4_23),
% 0.20/0.51    inference(resolution,[],[f304,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.20/0.51  fof(f304,plain,(
% 0.20/0.51    ( ! [X17] : (r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X17))),k1_relat_1(k7_relat_1(sK0,X17))) | k7_relat_1(sK0,X17) = k7_relat_1(sK1,X17)) ) | ~spl4_23),
% 0.20/0.51    inference(avatar_component_clause,[],[f303])).
% 0.20/0.51  fof(f305,plain,(
% 0.20/0.51    ~spl4_6 | spl4_23 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_21),
% 0.20/0.51    inference(avatar_split_clause,[],[f301,f214,f90,f84,f75,f65,f303,f75])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    spl4_21 <=> ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) | r2_hidden(sK3(sK1,sK0,X1),X1) | ~r1_tarski(X1,k1_relat_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.51  fof(f301,plain,(
% 0.20/0.51    ( ! [X17] : (k7_relat_1(sK0,X17) = k7_relat_1(sK1,X17) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X17))),k1_relat_1(k7_relat_1(sK0,X17))) | ~v1_relat_1(sK0)) ) | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_21)),
% 0.20/0.51    inference(forward_demodulation,[],[f300,f195])).
% 0.20/0.51  fof(f300,plain,(
% 0.20/0.51    ( ! [X17] : (k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X17))) = k7_relat_1(sK1,X17) | r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X17))),k1_relat_1(k7_relat_1(sK0,X17))) | ~v1_relat_1(sK0)) ) | (~spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_21)),
% 0.20/0.51    inference(forward_demodulation,[],[f296,f170])).
% 0.20/0.51  fof(f296,plain,(
% 0.20/0.51    ( ! [X17] : (r2_hidden(sK3(sK1,sK0,k1_relat_1(k7_relat_1(sK0,X17))),k1_relat_1(k7_relat_1(sK0,X17))) | k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X17))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK0,X17))) | ~v1_relat_1(sK0)) ) | ~spl4_21),
% 0.20/0.51    inference(resolution,[],[f215,f41])).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,sK0,X1),X1) | k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1)) ) | ~spl4_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f214])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    ~spl4_6 | spl4_21 | ~spl4_5 | ~spl4_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f212,f133,f70,f214,f75])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl4_11 <=> ! [X1,X0] : (~r1_tarski(X1,k1_relat_1(sK0)) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | r2_hidden(sK3(sK1,X0,X1),X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.51  fof(f212,plain,(
% 0.20/0.51    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK0) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,sK0,X1),X1)) ) | (~spl4_5 | ~spl4_11)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f211])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK0) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,sK0,X1),X1)) ) | (~spl4_5 | ~spl4_11)),
% 0.20/0.51    inference(resolution,[],[f134,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    v1_funct_1(sK0) | ~spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f70])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(X0) | ~r1_tarski(X1,k1_relat_1(sK0)) | ~r1_tarski(X1,k1_relat_1(X0)) | r2_hidden(sK3(sK1,X0,X1),X1)) ) | ~spl4_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f133])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ~spl4_4 | spl4_11 | ~spl4_2 | ~spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f131,f60,f55,f133,f65])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(sK0)) | r2_hidden(sK3(sK1,X0,X1),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK1)) ) | (~spl4_2 | ~spl4_3)),
% 0.20/0.51    inference(forward_demodulation,[],[f129,f57])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK3(sK1,X0,X1),X1) | ~r1_tarski(X1,k1_relat_1(X0)) | ~r1_tarski(X1,k1_relat_1(sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(sK1,X1) | ~v1_relat_1(sK1)) ) | ~spl4_3),
% 0.20/0.51    inference(resolution,[],[f38,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    v1_funct_1(sK1) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f60])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK3(X0,X1,X2),X2) | ~r1_tarski(X2,k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k7_relat_1(X0,X2) = k7_relat_1(X1,X2) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl4_7 | ~spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f82,f75,f84])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl4_6),
% 0.20/0.51    inference(resolution,[],[f36,f77])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl4_8 | ~spl4_2 | ~spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f94,f65,f55,f90])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    sK1 = k7_relat_1(sK1,k1_relat_1(sK0)) | (~spl4_2 | ~spl4_4)),
% 0.20/0.51    inference(forward_demodulation,[],[f81,f57])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f36,f67])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f29,f75])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f70])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    v1_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f31,f65])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    v1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f32,f60])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    v1_funct_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f33,f55])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f35,f50])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (20995)------------------------------
% 0.20/0.51  % (20995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20995)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (20995)Memory used [KB]: 6908
% 0.20/0.51  % (20995)Time elapsed: 0.040 s
% 0.20/0.51  % (20995)------------------------------
% 0.20/0.51  % (20995)------------------------------
% 0.20/0.51  % (20988)Success in time 0.157 s
%------------------------------------------------------------------------------
