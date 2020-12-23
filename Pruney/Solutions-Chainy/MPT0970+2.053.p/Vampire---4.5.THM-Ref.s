%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:56 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 277 expanded)
%              Number of leaves         :   39 ( 124 expanded)
%              Depth                    :   11
%              Number of atoms          :  566 (1235 expanded)
%              Number of equality atoms :  136 ( 336 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1405,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f89,f93,f97,f105,f110,f118,f124,f127,f136,f256,f336,f419,f520,f828,f839,f851,f855,f1117,f1136,f1263,f1404])).

fof(f1404,plain,(
    spl8_161 ),
    inference(avatar_contradiction_clause,[],[f1402])).

fof(f1402,plain,
    ( $false
    | spl8_161 ),
    inference(resolution,[],[f1262,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1262,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(sK2,k1_xboole_0))
    | spl8_161 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1261,plain,
    ( spl8_161
  <=> r1_tarski(k1_xboole_0,sK4(sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_161])])).

fof(f1263,plain,
    ( ~ spl8_161
    | ~ spl8_11
    | spl8_92 ),
    inference(avatar_split_clause,[],[f1226,f853,f133,f1261])).

fof(f133,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f853,plain,
    ( spl8_92
  <=> r1_tarski(sK1,sK4(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f1226,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4(sK2,k1_xboole_0))
    | ~ spl8_11
    | spl8_92 ),
    inference(superposition,[],[f854,f134])).

fof(f134,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f854,plain,
    ( ~ r1_tarski(sK1,sK4(sK2,sK1))
    | spl8_92 ),
    inference(avatar_component_clause,[],[f853])).

fof(f1136,plain,
    ( ~ spl8_87
    | spl8_137 ),
    inference(avatar_split_clause,[],[f1134,f1115,f822])).

fof(f822,plain,
    ( spl8_87
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f1115,plain,
    ( spl8_137
  <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).

fof(f1134,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | spl8_137 ),
    inference(resolution,[],[f1116,f46])).

fof(f46,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) = X3
              & r2_hidden(X4,sK0) )
          | ~ r2_hidden(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f1116,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | spl8_137 ),
    inference(avatar_component_clause,[],[f1115])).

fof(f1117,plain,
    ( ~ spl8_137
    | ~ spl8_88
    | ~ spl8_91 ),
    inference(avatar_split_clause,[],[f1113,f849,f825,f1115])).

fof(f825,plain,
    ( spl8_88
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) != sK4(sK2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f849,plain,
    ( spl8_91
  <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f1113,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl8_88
    | ~ spl8_91 ),
    inference(trivial_inequality_removal,[],[f1112])).

fof(f1112,plain,
    ( sK4(sK2,sK1) != sK4(sK2,sK1)
    | ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl8_88
    | ~ spl8_91 ),
    inference(superposition,[],[f826,f850])).

fof(f850,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_91 ),
    inference(avatar_component_clause,[],[f849])).

fof(f826,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) != sK4(sK2,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f825])).

fof(f855,plain,
    ( ~ spl8_92
    | ~ spl8_87 ),
    inference(avatar_split_clause,[],[f837,f822,f853])).

fof(f837,plain,
    ( ~ r1_tarski(sK1,sK4(sK2,sK1))
    | ~ spl8_87 ),
    inference(resolution,[],[f823,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f823,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_87 ),
    inference(avatar_component_clause,[],[f822])).

fof(f851,plain,
    ( spl8_91
    | ~ spl8_87 ),
    inference(avatar_split_clause,[],[f835,f822,f849])).

fof(f835,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_87 ),
    inference(resolution,[],[f823,f47])).

fof(f47,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f839,plain,
    ( ~ spl8_7
    | ~ spl8_4
    | spl8_6
    | spl8_88
    | ~ spl8_32
    | ~ spl8_87 ),
    inference(avatar_split_clause,[],[f838,f822,f253,f825,f108,f95,f113])).

fof(f113,plain,
    ( spl8_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f95,plain,
    ( spl8_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f108,plain,
    ( spl8_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f253,plain,
    ( spl8_32
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f838,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) != sK4(sK2,sK1)
        | sK1 = k2_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_32
    | ~ spl8_87 ),
    inference(forward_demodulation,[],[f831,f254])).

fof(f254,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f253])).

fof(f831,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) != sK4(sK2,sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK1 = k2_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_87 ),
    inference(resolution,[],[f823,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | k1_funct_1(X0,X3) != sK4(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k2_relat_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f828,plain,
    ( spl8_6
    | spl8_87
    | ~ spl8_2
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f817,f518,f87,f822,f108])).

fof(f87,plain,
    ( spl8_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f518,plain,
    ( spl8_58
  <=> ! [X1,X0] :
        ( k2_relat_1(sK2) = X0
        | ~ v5_relat_1(sK2,X1)
        | r2_hidden(sK4(sK2,X0),X0)
        | r2_hidden(sK4(sK2,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f817,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_2
    | ~ spl8_58 ),
    inference(factoring,[],[f808])).

fof(f808,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK1)
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_2
    | ~ spl8_58 ),
    inference(resolution,[],[f521,f88])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f521,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | r2_hidden(sK4(sK2,X0),X0)
        | r2_hidden(sK4(sK2,X0),X1)
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_58 ),
    inference(resolution,[],[f519,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f519,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK2,X1)
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0)
        | r2_hidden(sK4(sK2,X0),X1) )
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f518])).

fof(f520,plain,
    ( ~ spl8_7
    | spl8_58
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f515,f417,f518,f113])).

fof(f417,plain,
    ( spl8_48
  <=> ! [X0] :
        ( r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f515,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X1)
        | r2_hidden(sK4(sK2,X0),X0)
        | ~ v5_relat_1(sK2,X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_48 ),
    inference(resolution,[],[f428,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f428,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k2_relat_1(sK2),X4)
        | k2_relat_1(sK2) = X3
        | r2_hidden(sK4(sK2,X3),X4)
        | r2_hidden(sK4(sK2,X3),X3) )
    | ~ spl8_48 ),
    inference(resolution,[],[f418,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f418,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f417])).

fof(f419,plain,
    ( ~ spl8_7
    | ~ spl8_4
    | spl8_48
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f406,f334,f417,f95,f113])).

fof(f334,plain,
    ( spl8_38
  <=> ! [X0] :
        ( k2_relat_1(sK2) = X0
        | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2))
        | r2_hidden(sK4(sK2,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f406,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_38 ),
    inference(duplicate_literal_removal,[],[f405])).

fof(f405,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),k2_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_38 ),
    inference(superposition,[],[f335,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f335,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f334])).

fof(f336,plain,
    ( ~ spl8_7
    | ~ spl8_4
    | spl8_38
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f309,f116,f334,f95,f113])).

fof(f116,plain,
    ( spl8_8
  <=> ! [X0] :
        ( r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f309,plain,
    ( ! [X0] :
        ( k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0)
        | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_8 ),
    inference(resolution,[],[f117,f74])).

fof(f74,plain,(
    ! [X6,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f117,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f256,plain,
    ( ~ spl8_2
    | spl8_32
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f250,f130,f253,f87])).

fof(f130,plain,
    ( spl8_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f250,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_10 ),
    inference(superposition,[],[f64,f131])).

fof(f131,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f136,plain,
    ( spl8_10
    | spl8_11
    | ~ spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f128,f87,f91,f133,f130])).

fof(f91,plain,
    ( spl8_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f128,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_2 ),
    inference(resolution,[],[f67,f88])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f127,plain,(
    spl8_9 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl8_9 ),
    inference(resolution,[],[f123,f57])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f123,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_9
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f124,plain,
    ( ~ spl8_9
    | ~ spl8_2
    | spl8_7 ),
    inference(avatar_split_clause,[],[f120,f113,f87,f122])).

fof(f120,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_2
    | spl8_7 ),
    inference(resolution,[],[f119,f88])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl8_7 ),
    inference(resolution,[],[f114,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f114,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f118,plain,
    ( ~ spl8_7
    | spl8_8
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f111,f95,f116,f113])).

fof(f111,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl8_4 ),
    inference(resolution,[],[f54,f96])).

fof(f96,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f110,plain,
    ( ~ spl8_6
    | spl8_1
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f106,f103,f83,f108])).

fof(f83,plain,
    ( spl8_1
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f103,plain,
    ( spl8_5
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f106,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_1
    | ~ spl8_5 ),
    inference(superposition,[],[f84,f104])).

fof(f104,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f84,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f105,plain,
    ( spl8_5
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f101,f87,f103])).

fof(f101,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_2 ),
    inference(resolution,[],[f65,f88])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f97,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f43,f95])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f45,f87])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f48,f83])).

fof(f48,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:38:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (18307)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (18299)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (18304)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.17/0.51  % (18291)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.17/0.51  % (18289)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.52  % (18295)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.17/0.52  % (18294)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.17/0.52  % (18290)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.52  % (18293)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.17/0.52  % (18312)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.17/0.52  % (18296)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.17/0.52  % (18305)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.53  % (18297)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.53  % (18313)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.53  % (18288)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.54  % (18287)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (18286)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.54  % (18314)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.54  % (18295)Refutation not found, incomplete strategy% (18295)------------------------------
% 1.33/0.54  % (18295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (18295)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (18295)Memory used [KB]: 10746
% 1.33/0.54  % (18295)Time elapsed: 0.126 s
% 1.33/0.54  % (18295)------------------------------
% 1.33/0.54  % (18295)------------------------------
% 1.33/0.54  % (18311)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.55  % (18310)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.55  % (18306)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.55  % (18285)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.55  % (18300)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.55  % (18303)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.33/0.55  % (18308)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.33/0.55  % (18302)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.55  % (18298)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.56  % (18301)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.56  % (18292)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.57  % (18309)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.60  % (18304)Refutation found. Thanks to Tanya!
% 1.33/0.60  % SZS status Theorem for theBenchmark
% 1.33/0.60  % SZS output start Proof for theBenchmark
% 1.33/0.60  fof(f1405,plain,(
% 1.33/0.60    $false),
% 1.33/0.60    inference(avatar_sat_refutation,[],[f85,f89,f93,f97,f105,f110,f118,f124,f127,f136,f256,f336,f419,f520,f828,f839,f851,f855,f1117,f1136,f1263,f1404])).
% 1.33/0.62  fof(f1404,plain,(
% 1.33/0.62    spl8_161),
% 1.33/0.62    inference(avatar_contradiction_clause,[],[f1402])).
% 1.33/0.62  fof(f1402,plain,(
% 1.33/0.62    $false | spl8_161),
% 1.33/0.62    inference(resolution,[],[f1262,f49])).
% 1.33/0.62  fof(f49,plain,(
% 1.33/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.33/0.62    inference(cnf_transformation,[],[f2])).
% 1.33/0.62  fof(f2,axiom,(
% 1.33/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.33/0.62  fof(f1262,plain,(
% 1.33/0.62    ~r1_tarski(k1_xboole_0,sK4(sK2,k1_xboole_0)) | spl8_161),
% 1.33/0.62    inference(avatar_component_clause,[],[f1261])).
% 1.33/0.62  fof(f1261,plain,(
% 1.33/0.62    spl8_161 <=> r1_tarski(k1_xboole_0,sK4(sK2,k1_xboole_0))),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_161])])).
% 1.33/0.62  fof(f1263,plain,(
% 1.33/0.62    ~spl8_161 | ~spl8_11 | spl8_92),
% 1.33/0.62    inference(avatar_split_clause,[],[f1226,f853,f133,f1261])).
% 1.33/0.62  fof(f133,plain,(
% 1.33/0.62    spl8_11 <=> k1_xboole_0 = sK1),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.33/0.62  fof(f853,plain,(
% 1.33/0.62    spl8_92 <=> r1_tarski(sK1,sK4(sK2,sK1))),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).
% 1.33/0.62  fof(f1226,plain,(
% 1.33/0.62    ~r1_tarski(k1_xboole_0,sK4(sK2,k1_xboole_0)) | (~spl8_11 | spl8_92)),
% 1.33/0.62    inference(superposition,[],[f854,f134])).
% 1.33/0.62  fof(f134,plain,(
% 1.33/0.62    k1_xboole_0 = sK1 | ~spl8_11),
% 1.33/0.62    inference(avatar_component_clause,[],[f133])).
% 1.33/0.62  fof(f854,plain,(
% 1.33/0.62    ~r1_tarski(sK1,sK4(sK2,sK1)) | spl8_92),
% 1.33/0.62    inference(avatar_component_clause,[],[f853])).
% 1.33/0.62  fof(f1136,plain,(
% 1.33/0.62    ~spl8_87 | spl8_137),
% 1.33/0.62    inference(avatar_split_clause,[],[f1134,f1115,f822])).
% 1.33/0.62  fof(f822,plain,(
% 1.33/0.62    spl8_87 <=> r2_hidden(sK4(sK2,sK1),sK1)),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).
% 1.33/0.62  fof(f1115,plain,(
% 1.33/0.62    spl8_137 <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0)),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).
% 1.33/0.62  fof(f1134,plain,(
% 1.33/0.62    ~r2_hidden(sK4(sK2,sK1),sK1) | spl8_137),
% 1.33/0.62    inference(resolution,[],[f1116,f46])).
% 1.33/0.62  fof(f46,plain,(
% 1.33/0.62    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.33/0.62    inference(cnf_transformation,[],[f30])).
% 1.33/0.62  fof(f30,plain,(
% 1.33/0.62    sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : ((k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.33/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f29,f28])).
% 1.33/0.62  fof(f28,plain,(
% 1.33/0.62    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.33/0.62    introduced(choice_axiom,[])).
% 1.33/0.62  fof(f29,plain,(
% 1.33/0.62    ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) => (k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)))),
% 1.33/0.62    introduced(choice_axiom,[])).
% 1.33/0.62  fof(f16,plain,(
% 1.33/0.62    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.33/0.62    inference(flattening,[],[f15])).
% 1.33/0.62  fof(f15,plain,(
% 1.33/0.62    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.33/0.62    inference(ennf_transformation,[],[f13])).
% 1.33/0.62  fof(f13,negated_conjecture,(
% 1.33/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.33/0.62    inference(negated_conjecture,[],[f12])).
% 1.33/0.62  fof(f12,conjecture,(
% 1.33/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 1.33/0.62  fof(f1116,plain,(
% 1.33/0.62    ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | spl8_137),
% 1.33/0.62    inference(avatar_component_clause,[],[f1115])).
% 1.33/0.62  fof(f1117,plain,(
% 1.33/0.62    ~spl8_137 | ~spl8_88 | ~spl8_91),
% 1.33/0.62    inference(avatar_split_clause,[],[f1113,f849,f825,f1115])).
% 1.33/0.62  fof(f825,plain,(
% 1.33/0.62    spl8_88 <=> ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) != sK4(sK2,sK1))),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).
% 1.33/0.62  fof(f849,plain,(
% 1.33/0.62    spl8_91 <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).
% 1.33/0.62  fof(f1113,plain,(
% 1.33/0.62    ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | (~spl8_88 | ~spl8_91)),
% 1.33/0.62    inference(trivial_inequality_removal,[],[f1112])).
% 1.33/0.62  fof(f1112,plain,(
% 1.33/0.62    sK4(sK2,sK1) != sK4(sK2,sK1) | ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | (~spl8_88 | ~spl8_91)),
% 1.33/0.62    inference(superposition,[],[f826,f850])).
% 1.33/0.62  fof(f850,plain,(
% 1.33/0.62    sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl8_91),
% 1.33/0.62    inference(avatar_component_clause,[],[f849])).
% 1.33/0.62  fof(f826,plain,(
% 1.33/0.62    ( ! [X0] : (k1_funct_1(sK2,X0) != sK4(sK2,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_88),
% 1.33/0.62    inference(avatar_component_clause,[],[f825])).
% 1.33/0.62  fof(f855,plain,(
% 1.33/0.62    ~spl8_92 | ~spl8_87),
% 1.33/0.62    inference(avatar_split_clause,[],[f837,f822,f853])).
% 1.33/0.62  fof(f837,plain,(
% 1.33/0.62    ~r1_tarski(sK1,sK4(sK2,sK1)) | ~spl8_87),
% 1.33/0.62    inference(resolution,[],[f823,f63])).
% 1.33/0.62  fof(f63,plain,(
% 1.33/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.33/0.62    inference(cnf_transformation,[],[f22])).
% 1.33/0.62  fof(f22,plain,(
% 1.33/0.62    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.33/0.62    inference(ennf_transformation,[],[f7])).
% 1.33/0.62  fof(f7,axiom,(
% 1.33/0.62    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.33/0.62  fof(f823,plain,(
% 1.33/0.62    r2_hidden(sK4(sK2,sK1),sK1) | ~spl8_87),
% 1.33/0.62    inference(avatar_component_clause,[],[f822])).
% 1.33/0.62  fof(f851,plain,(
% 1.33/0.62    spl8_91 | ~spl8_87),
% 1.33/0.62    inference(avatar_split_clause,[],[f835,f822,f849])).
% 1.33/0.62  fof(f835,plain,(
% 1.33/0.62    sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl8_87),
% 1.33/0.62    inference(resolution,[],[f823,f47])).
% 1.33/0.62  fof(f47,plain,(
% 1.33/0.62    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 1.33/0.62    inference(cnf_transformation,[],[f30])).
% 1.33/0.62  fof(f839,plain,(
% 1.33/0.62    ~spl8_7 | ~spl8_4 | spl8_6 | spl8_88 | ~spl8_32 | ~spl8_87),
% 1.33/0.62    inference(avatar_split_clause,[],[f838,f822,f253,f825,f108,f95,f113])).
% 1.33/0.62  fof(f113,plain,(
% 1.33/0.62    spl8_7 <=> v1_relat_1(sK2)),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.33/0.62  fof(f95,plain,(
% 1.33/0.62    spl8_4 <=> v1_funct_1(sK2)),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.33/0.62  fof(f108,plain,(
% 1.33/0.62    spl8_6 <=> sK1 = k2_relat_1(sK2)),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.33/0.62  fof(f253,plain,(
% 1.33/0.62    spl8_32 <=> sK0 = k1_relat_1(sK2)),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.33/0.62  fof(f838,plain,(
% 1.33/0.62    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) != sK4(sK2,sK1) | sK1 = k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl8_32 | ~spl8_87)),
% 1.33/0.62    inference(forward_demodulation,[],[f831,f254])).
% 1.33/0.62  fof(f254,plain,(
% 1.33/0.62    sK0 = k1_relat_1(sK2) | ~spl8_32),
% 1.33/0.62    inference(avatar_component_clause,[],[f253])).
% 1.33/0.62  fof(f831,plain,(
% 1.33/0.62    ( ! [X0] : (k1_funct_1(sK2,X0) != sK4(sK2,sK1) | ~r2_hidden(X0,k1_relat_1(sK2)) | sK1 = k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_87),
% 1.33/0.62    inference(resolution,[],[f823,f56])).
% 1.33/0.62  fof(f56,plain,(
% 1.33/0.62    ( ! [X0,X3,X1] : (~r2_hidden(sK4(X0,X1),X1) | k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k2_relat_1(X0) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.62    inference(cnf_transformation,[],[f36])).
% 1.33/0.62  fof(f36,plain,(
% 1.33/0.62    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).
% 1.33/0.62  fof(f33,plain,(
% 1.33/0.62    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 1.33/0.62    introduced(choice_axiom,[])).
% 1.33/0.62  fof(f34,plain,(
% 1.33/0.62    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 1.33/0.62    introduced(choice_axiom,[])).
% 1.33/0.62  fof(f35,plain,(
% 1.33/0.62    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 1.33/0.62    introduced(choice_axiom,[])).
% 1.33/0.62  fof(f32,plain,(
% 1.33/0.62    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.62    inference(rectify,[],[f31])).
% 1.33/0.62  fof(f31,plain,(
% 1.33/0.62    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.62    inference(nnf_transformation,[],[f19])).
% 1.33/0.62  fof(f19,plain,(
% 1.33/0.62    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.62    inference(flattening,[],[f18])).
% 1.33/0.62  fof(f18,plain,(
% 1.33/0.62    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.33/0.62    inference(ennf_transformation,[],[f6])).
% 1.33/0.62  fof(f6,axiom,(
% 1.33/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.33/0.62  fof(f828,plain,(
% 1.33/0.62    spl8_6 | spl8_87 | ~spl8_2 | ~spl8_58),
% 1.33/0.62    inference(avatar_split_clause,[],[f817,f518,f87,f822,f108])).
% 1.33/0.62  fof(f87,plain,(
% 1.33/0.62    spl8_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.33/0.62  fof(f518,plain,(
% 1.33/0.62    spl8_58 <=> ! [X1,X0] : (k2_relat_1(sK2) = X0 | ~v5_relat_1(sK2,X1) | r2_hidden(sK4(sK2,X0),X0) | r2_hidden(sK4(sK2,X0),X1))),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).
% 1.33/0.62  fof(f817,plain,(
% 1.33/0.62    r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | (~spl8_2 | ~spl8_58)),
% 1.33/0.62    inference(factoring,[],[f808])).
% 1.33/0.62  fof(f808,plain,(
% 1.33/0.62    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK1) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | (~spl8_2 | ~spl8_58)),
% 1.33/0.62    inference(resolution,[],[f521,f88])).
% 1.33/0.62  fof(f88,plain,(
% 1.33/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_2),
% 1.33/0.62    inference(avatar_component_clause,[],[f87])).
% 1.33/0.62  fof(f521,plain,(
% 1.33/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r2_hidden(sK4(sK2,X0),X0) | r2_hidden(sK4(sK2,X0),X1) | k2_relat_1(sK2) = X0) ) | ~spl8_58),
% 1.33/0.62    inference(resolution,[],[f519,f66])).
% 1.33/0.62  fof(f66,plain,(
% 1.33/0.62    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.62    inference(cnf_transformation,[],[f25])).
% 1.33/0.62  fof(f25,plain,(
% 1.33/0.62    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.62    inference(ennf_transformation,[],[f14])).
% 1.33/0.62  fof(f14,plain,(
% 1.33/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.33/0.62    inference(pure_predicate_removal,[],[f8])).
% 1.33/0.62  fof(f8,axiom,(
% 1.33/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.33/0.62  fof(f519,plain,(
% 1.33/0.62    ( ! [X0,X1] : (~v5_relat_1(sK2,X1) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0) | r2_hidden(sK4(sK2,X0),X1)) ) | ~spl8_58),
% 1.33/0.62    inference(avatar_component_clause,[],[f518])).
% 1.33/0.62  fof(f520,plain,(
% 1.33/0.62    ~spl8_7 | spl8_58 | ~spl8_48),
% 1.33/0.62    inference(avatar_split_clause,[],[f515,f417,f518,f113])).
% 1.33/0.62  fof(f417,plain,(
% 1.33/0.62    spl8_48 <=> ! [X0] : (r2_hidden(sK4(sK2,X0),k2_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0)),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 1.33/0.62  fof(f515,plain,(
% 1.33/0.62    ( ! [X0,X1] : (k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X1) | r2_hidden(sK4(sK2,X0),X0) | ~v5_relat_1(sK2,X1) | ~v1_relat_1(sK2)) ) | ~spl8_48),
% 1.33/0.62    inference(resolution,[],[f428,f58])).
% 1.33/0.62  fof(f58,plain,(
% 1.33/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.33/0.62    inference(cnf_transformation,[],[f37])).
% 1.33/0.62  fof(f37,plain,(
% 1.33/0.62    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.33/0.62    inference(nnf_transformation,[],[f20])).
% 1.33/0.62  fof(f20,plain,(
% 1.33/0.62    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.33/0.62    inference(ennf_transformation,[],[f4])).
% 1.33/0.62  fof(f4,axiom,(
% 1.33/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.33/0.62  fof(f428,plain,(
% 1.33/0.62    ( ! [X4,X3] : (~r1_tarski(k2_relat_1(sK2),X4) | k2_relat_1(sK2) = X3 | r2_hidden(sK4(sK2,X3),X4) | r2_hidden(sK4(sK2,X3),X3)) ) | ~spl8_48),
% 1.33/0.62    inference(resolution,[],[f418,f60])).
% 1.33/0.62  fof(f60,plain,(
% 1.33/0.62    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.33/0.62    inference(cnf_transformation,[],[f41])).
% 1.33/0.62  fof(f41,plain,(
% 1.33/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.33/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).
% 1.33/0.62  fof(f40,plain,(
% 1.33/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.33/0.62    introduced(choice_axiom,[])).
% 1.33/0.62  fof(f39,plain,(
% 1.33/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.33/0.62    inference(rectify,[],[f38])).
% 1.33/0.62  fof(f38,plain,(
% 1.33/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.33/0.62    inference(nnf_transformation,[],[f21])).
% 1.33/0.62  fof(f21,plain,(
% 1.33/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.33/0.62    inference(ennf_transformation,[],[f1])).
% 1.33/0.62  fof(f1,axiom,(
% 1.33/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.33/0.62  fof(f418,plain,(
% 1.33/0.62    ( ! [X0] : (r2_hidden(sK4(sK2,X0),k2_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | ~spl8_48),
% 1.33/0.62    inference(avatar_component_clause,[],[f417])).
% 1.33/0.62  fof(f419,plain,(
% 1.33/0.62    ~spl8_7 | ~spl8_4 | spl8_48 | ~spl8_38),
% 1.33/0.62    inference(avatar_split_clause,[],[f406,f334,f417,f95,f113])).
% 1.33/0.62  fof(f334,plain,(
% 1.33/0.62    spl8_38 <=> ! [X0] : (k2_relat_1(sK2) = X0 | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),X0))),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 1.33/0.62  fof(f406,plain,(
% 1.33/0.62    ( ! [X0] : (r2_hidden(sK4(sK2,X0),k2_relat_1(sK2)) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_38),
% 1.33/0.62    inference(duplicate_literal_removal,[],[f405])).
% 1.33/0.62  fof(f405,plain,(
% 1.33/0.62    ( ! [X0] : (r2_hidden(sK4(sK2,X0),k2_relat_1(sK2)) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_38),
% 1.33/0.62    inference(superposition,[],[f335,f55])).
% 1.33/0.62  fof(f55,plain,(
% 1.33/0.62    ( ! [X0,X1] : (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) | k2_relat_1(X0) = X1 | r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.62    inference(cnf_transformation,[],[f36])).
% 1.33/0.62  fof(f335,plain,(
% 1.33/0.62    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2)) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0)) ) | ~spl8_38),
% 1.33/0.62    inference(avatar_component_clause,[],[f334])).
% 1.33/0.62  fof(f336,plain,(
% 1.33/0.62    ~spl8_7 | ~spl8_4 | spl8_38 | ~spl8_8),
% 1.33/0.62    inference(avatar_split_clause,[],[f309,f116,f334,f95,f113])).
% 1.33/0.62  fof(f116,plain,(
% 1.33/0.62    spl8_8 <=> ! [X0] : (r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0))),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.33/0.62  fof(f309,plain,(
% 1.33/0.62    ( ! [X0] : (k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0) | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_8),
% 1.33/0.62    inference(resolution,[],[f117,f74])).
% 1.33/0.62  fof(f74,plain,(
% 1.33/0.62    ( ! [X6,X0] : (~r2_hidden(X6,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.62    inference(equality_resolution,[],[f73])).
% 1.33/0.62  fof(f73,plain,(
% 1.33/0.62    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.62    inference(equality_resolution,[],[f53])).
% 1.33/0.62  fof(f53,plain,(
% 1.33/0.62    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.62    inference(cnf_transformation,[],[f36])).
% 1.33/0.62  fof(f117,plain,(
% 1.33/0.62    ( ! [X0] : (r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0)) ) | ~spl8_8),
% 1.33/0.62    inference(avatar_component_clause,[],[f116])).
% 1.33/0.62  fof(f256,plain,(
% 1.33/0.62    ~spl8_2 | spl8_32 | ~spl8_10),
% 1.33/0.62    inference(avatar_split_clause,[],[f250,f130,f253,f87])).
% 1.33/0.62  fof(f130,plain,(
% 1.33/0.62    spl8_10 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.33/0.62  fof(f250,plain,(
% 1.33/0.62    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_10),
% 1.33/0.62    inference(superposition,[],[f64,f131])).
% 1.33/0.62  fof(f131,plain,(
% 1.33/0.62    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_10),
% 1.33/0.62    inference(avatar_component_clause,[],[f130])).
% 1.33/0.62  fof(f64,plain,(
% 1.33/0.62    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.62    inference(cnf_transformation,[],[f23])).
% 1.33/0.62  fof(f23,plain,(
% 1.33/0.62    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.62    inference(ennf_transformation,[],[f9])).
% 1.33/0.62  fof(f9,axiom,(
% 1.33/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.33/0.62  fof(f136,plain,(
% 1.33/0.62    spl8_10 | spl8_11 | ~spl8_3 | ~spl8_2),
% 1.33/0.62    inference(avatar_split_clause,[],[f128,f87,f91,f133,f130])).
% 1.33/0.62  fof(f91,plain,(
% 1.33/0.62    spl8_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.33/0.62  fof(f128,plain,(
% 1.33/0.62    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_2),
% 1.33/0.62    inference(resolution,[],[f67,f88])).
% 1.33/0.62  fof(f67,plain,(
% 1.33/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.33/0.62    inference(cnf_transformation,[],[f42])).
% 1.33/0.62  fof(f42,plain,(
% 1.33/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.62    inference(nnf_transformation,[],[f27])).
% 1.33/0.62  fof(f27,plain,(
% 1.33/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.62    inference(flattening,[],[f26])).
% 1.33/0.62  fof(f26,plain,(
% 1.33/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.62    inference(ennf_transformation,[],[f11])).
% 1.33/0.62  fof(f11,axiom,(
% 1.33/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.33/0.62  fof(f127,plain,(
% 1.33/0.62    spl8_9),
% 1.33/0.62    inference(avatar_contradiction_clause,[],[f125])).
% 1.33/0.62  fof(f125,plain,(
% 1.33/0.62    $false | spl8_9),
% 1.33/0.62    inference(resolution,[],[f123,f57])).
% 1.33/0.62  fof(f57,plain,(
% 1.33/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.33/0.62    inference(cnf_transformation,[],[f5])).
% 1.33/0.62  fof(f5,axiom,(
% 1.33/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.33/0.62  fof(f123,plain,(
% 1.33/0.62    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl8_9),
% 1.33/0.62    inference(avatar_component_clause,[],[f122])).
% 1.33/0.62  fof(f122,plain,(
% 1.33/0.62    spl8_9 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.33/0.62  fof(f124,plain,(
% 1.33/0.62    ~spl8_9 | ~spl8_2 | spl8_7),
% 1.33/0.62    inference(avatar_split_clause,[],[f120,f113,f87,f122])).
% 1.33/0.62  fof(f120,plain,(
% 1.33/0.62    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl8_2 | spl8_7)),
% 1.33/0.62    inference(resolution,[],[f119,f88])).
% 1.33/0.62  fof(f119,plain,(
% 1.33/0.62    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl8_7),
% 1.33/0.62    inference(resolution,[],[f114,f50])).
% 1.33/0.62  fof(f50,plain,(
% 1.33/0.62    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.33/0.62    inference(cnf_transformation,[],[f17])).
% 1.33/0.62  fof(f17,plain,(
% 1.33/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.33/0.62    inference(ennf_transformation,[],[f3])).
% 1.33/0.62  fof(f3,axiom,(
% 1.33/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.33/0.62  fof(f114,plain,(
% 1.33/0.62    ~v1_relat_1(sK2) | spl8_7),
% 1.33/0.62    inference(avatar_component_clause,[],[f113])).
% 1.33/0.62  fof(f118,plain,(
% 1.33/0.62    ~spl8_7 | spl8_8 | ~spl8_4),
% 1.33/0.62    inference(avatar_split_clause,[],[f111,f95,f116,f113])).
% 1.33/0.62  fof(f111,plain,(
% 1.33/0.62    ( ! [X0] : (r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0 | ~v1_relat_1(sK2)) ) | ~spl8_4),
% 1.33/0.62    inference(resolution,[],[f54,f96])).
% 1.33/0.62  fof(f96,plain,(
% 1.33/0.62    v1_funct_1(sK2) | ~spl8_4),
% 1.33/0.62    inference(avatar_component_clause,[],[f95])).
% 1.33/0.62  fof(f54,plain,(
% 1.33/0.62    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 1.33/0.62    inference(cnf_transformation,[],[f36])).
% 1.33/0.62  fof(f110,plain,(
% 1.33/0.62    ~spl8_6 | spl8_1 | ~spl8_5),
% 1.33/0.62    inference(avatar_split_clause,[],[f106,f103,f83,f108])).
% 1.33/0.62  fof(f83,plain,(
% 1.33/0.62    spl8_1 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.33/0.62  fof(f103,plain,(
% 1.33/0.62    spl8_5 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.33/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.33/0.62  fof(f106,plain,(
% 1.33/0.62    sK1 != k2_relat_1(sK2) | (spl8_1 | ~spl8_5)),
% 1.33/0.62    inference(superposition,[],[f84,f104])).
% 1.33/0.62  fof(f104,plain,(
% 1.33/0.62    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_5),
% 1.33/0.62    inference(avatar_component_clause,[],[f103])).
% 1.33/0.62  fof(f84,plain,(
% 1.33/0.62    sK1 != k2_relset_1(sK0,sK1,sK2) | spl8_1),
% 1.33/0.62    inference(avatar_component_clause,[],[f83])).
% 1.33/0.62  fof(f105,plain,(
% 1.33/0.62    spl8_5 | ~spl8_2),
% 1.33/0.62    inference(avatar_split_clause,[],[f101,f87,f103])).
% 1.33/0.62  fof(f101,plain,(
% 1.33/0.62    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_2),
% 1.33/0.62    inference(resolution,[],[f65,f88])).
% 1.33/0.62  fof(f65,plain,(
% 1.33/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.33/0.62    inference(cnf_transformation,[],[f24])).
% 1.33/0.62  fof(f24,plain,(
% 1.33/0.62    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.62    inference(ennf_transformation,[],[f10])).
% 1.33/0.62  fof(f10,axiom,(
% 1.33/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.33/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.33/0.62  fof(f97,plain,(
% 1.33/0.62    spl8_4),
% 1.33/0.62    inference(avatar_split_clause,[],[f43,f95])).
% 1.33/0.62  fof(f43,plain,(
% 1.33/0.62    v1_funct_1(sK2)),
% 1.33/0.62    inference(cnf_transformation,[],[f30])).
% 1.33/0.62  fof(f93,plain,(
% 1.33/0.62    spl8_3),
% 1.33/0.62    inference(avatar_split_clause,[],[f44,f91])).
% 1.33/0.62  fof(f44,plain,(
% 1.33/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.33/0.62    inference(cnf_transformation,[],[f30])).
% 1.33/0.62  fof(f89,plain,(
% 1.33/0.62    spl8_2),
% 1.33/0.62    inference(avatar_split_clause,[],[f45,f87])).
% 1.33/0.62  fof(f45,plain,(
% 1.33/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.33/0.62    inference(cnf_transformation,[],[f30])).
% 1.33/0.62  fof(f85,plain,(
% 1.33/0.62    ~spl8_1),
% 1.33/0.62    inference(avatar_split_clause,[],[f48,f83])).
% 1.33/0.62  fof(f48,plain,(
% 1.33/0.62    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.33/0.62    inference(cnf_transformation,[],[f30])).
% 1.33/0.62  % SZS output end Proof for theBenchmark
% 1.33/0.62  % (18304)------------------------------
% 1.33/0.62  % (18304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.62  % (18304)Termination reason: Refutation
% 1.33/0.62  
% 1.33/0.62  % (18304)Memory used [KB]: 11897
% 1.33/0.62  % (18304)Time elapsed: 0.178 s
% 1.33/0.62  % (18304)------------------------------
% 1.33/0.62  % (18304)------------------------------
% 1.33/0.62  % (18284)Success in time 0.265 s
%------------------------------------------------------------------------------
