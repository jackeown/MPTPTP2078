%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t49_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:11 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 680 expanded)
%              Number of leaves         :   67 ( 281 expanded)
%              Depth                    :   11
%              Number of atoms          :  584 (1967 expanded)
%              Number of equality atoms :   50 ( 212 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f592,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f98,f105,f112,f119,f129,f138,f146,f153,f161,f176,f183,f200,f215,f222,f229,f236,f247,f266,f273,f292,f301,f314,f321,f334,f342,f357,f364,f377,f386,f393,f402,f420,f456,f464,f479,f488,f499,f520,f531,f544,f553,f560,f574,f584,f585,f587,f589,f591])).

fof(f591,plain,
    ( ~ spl6_14
    | spl6_77
    | ~ spl6_86 ),
    inference(avatar_contradiction_clause,[],[f590])).

fof(f590,plain,
    ( $false
    | ~ spl6_14
    | ~ spl6_77
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f582,f519])).

fof(f519,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl6_77
  <=> ~ v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f582,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl6_14
    | ~ spl6_86 ),
    inference(resolution,[],[f576,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',d1_xboole_0)).

fof(f576,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK2))
    | ~ spl6_14
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f575,f503])).

fof(f503,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | ~ m1_subset_1(X3,sK1) )
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f501,f63])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_relset_1(sK0,sK1,sK2) != k1_xboole_0
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_relset_1(X0,X1,X2) != k1_xboole_0
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_relset_1(sK0,X1,X2) != k1_xboole_0
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_relset_1(X0,X1,X2) != k1_xboole_0
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(X0,sK1,X2))
                | ~ m1_subset_1(X3,sK1) )
            & k1_relset_1(X0,sK1,X2) != k1_xboole_0
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
              | ~ m1_subset_1(X3,X1) )
          & k1_relset_1(X0,X1,X2) != k1_xboole_0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,sK2))
            | ~ m1_subset_1(X3,X1) )
        & k1_relset_1(X0,X1,sK2) != k1_xboole_0
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_relset_1(X0,X1,X2) != k1_xboole_0
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_relset_1(X0,X1,X2) != k1_xboole_0
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_relset_1(X0,X1,X2) != k1_xboole_0 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_relset_1(X0,X1,X2) != k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',t49_relset_1)).

fof(f501,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f145,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',redefinition_k2_relset_1)).

fof(f145,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl6_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f575,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl6_86 ),
    inference(resolution,[],[f573,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',t4_subset)).

fof(f573,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl6_86 ),
    inference(avatar_component_clause,[],[f572])).

fof(f572,plain,
    ( spl6_86
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f589,plain,
    ( ~ spl6_14
    | spl6_77
    | ~ spl6_86 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | ~ spl6_14
    | ~ spl6_77
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f577,f519])).

fof(f577,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl6_14
    | ~ spl6_86 ),
    inference(unit_resulting_resolution,[],[f576,f69])).

fof(f587,plain,
    ( ~ spl6_14
    | spl6_77
    | ~ spl6_86 ),
    inference(avatar_contradiction_clause,[],[f586])).

fof(f586,plain,
    ( $false
    | ~ spl6_14
    | ~ spl6_77
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f579,f519])).

fof(f579,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl6_14
    | ~ spl6_86 ),
    inference(unit_resulting_resolution,[],[f70,f576,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',t2_subset)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',existence_m1_subset_1)).

fof(f585,plain,
    ( ~ spl6_14
    | spl6_77
    | ~ spl6_86 ),
    inference(avatar_contradiction_clause,[],[f581])).

fof(f581,plain,
    ( $false
    | ~ spl6_14
    | ~ spl6_77
    | ~ spl6_86 ),
    inference(unit_resulting_resolution,[],[f70,f519,f576,f73])).

fof(f584,plain,
    ( ~ spl6_14
    | spl6_77
    | ~ spl6_86 ),
    inference(avatar_contradiction_clause,[],[f578])).

fof(f578,plain,
    ( $false
    | ~ spl6_14
    | ~ spl6_77
    | ~ spl6_86 ),
    inference(unit_resulting_resolution,[],[f519,f576,f69])).

fof(f574,plain,
    ( spl6_86
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f567,f144,f572])).

fof(f567,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f561,f501])).

fof(f561,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f145,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',dt_k2_relset_1)).

fof(f560,plain,
    ( ~ spl6_85
    | spl6_77
    | spl6_81 ),
    inference(avatar_split_clause,[],[f545,f542,f518,f558])).

fof(f558,plain,
    ( spl6_85
  <=> ~ m1_subset_1(sK3(sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f542,plain,
    ( spl6_81
  <=> ~ r2_hidden(sK3(sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f545,plain,
    ( ~ m1_subset_1(sK3(sK1),k2_relat_1(sK2))
    | ~ spl6_77
    | ~ spl6_81 ),
    inference(unit_resulting_resolution,[],[f519,f543,f73])).

fof(f543,plain,
    ( ~ r2_hidden(sK3(sK1),k2_relat_1(sK2))
    | ~ spl6_81 ),
    inference(avatar_component_clause,[],[f542])).

fof(f553,plain,
    ( ~ spl6_83
    | spl6_77
    | spl6_79 ),
    inference(avatar_split_clause,[],[f536,f529,f518,f551])).

fof(f551,plain,
    ( spl6_83
  <=> ~ m1_subset_1(sK4(sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f529,plain,
    ( spl6_79
  <=> ~ r2_hidden(sK4(sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f536,plain,
    ( ~ m1_subset_1(sK4(sK1),k2_relat_1(sK2))
    | ~ spl6_77
    | ~ spl6_79 ),
    inference(unit_resulting_resolution,[],[f519,f530,f73])).

fof(f530,plain,
    ( ~ r2_hidden(sK4(sK1),k2_relat_1(sK2))
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f529])).

fof(f544,plain,
    ( ~ spl6_81
    | ~ spl6_14
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f505,f234,f144,f542])).

fof(f234,plain,
    ( spl6_32
  <=> m1_subset_1(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f505,plain,
    ( ~ r2_hidden(sK3(sK1),k2_relat_1(sK2))
    | ~ spl6_14
    | ~ spl6_32 ),
    inference(backward_demodulation,[],[f501,f323])).

fof(f323,plain,
    ( ~ r2_hidden(sK3(sK1),k2_relset_1(sK0,sK1,sK2))
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f235,f63])).

fof(f235,plain,
    ( m1_subset_1(sK3(sK1),sK1)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f234])).

fof(f531,plain,
    ( ~ spl6_79
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f504,f144,f529])).

fof(f504,plain,
    ( ~ r2_hidden(sK4(sK1),k2_relat_1(sK2))
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f501,f322])).

fof(f322,plain,(
    ~ r2_hidden(sK4(sK1),k2_relset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f70,f63])).

fof(f520,plain,
    ( ~ spl6_77
    | ~ spl6_10
    | spl6_75 ),
    inference(avatar_split_clause,[],[f513,f497,f127,f518])).

fof(f127,plain,
    ( spl6_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f497,plain,
    ( spl6_75
  <=> k1_xboole_0 != k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f513,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ spl6_10
    | ~ spl6_75 ),
    inference(unit_resulting_resolution,[],[f128,f498,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',t8_boole)).

fof(f498,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f497])).

fof(f128,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f499,plain,
    ( ~ spl6_75
    | ~ spl6_42
    | spl6_73 ),
    inference(avatar_split_clause,[],[f489,f486,f299,f497])).

fof(f299,plain,
    ( spl6_42
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f486,plain,
    ( spl6_73
  <=> k1_xboole_0 != k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f489,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl6_42
    | ~ spl6_73 ),
    inference(unit_resulting_resolution,[],[f300,f487,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',t65_relat_1)).

fof(f487,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f486])).

fof(f300,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f299])).

fof(f488,plain,
    ( ~ spl6_73
    | ~ spl6_14
    | spl6_17 ),
    inference(avatar_split_clause,[],[f472,f151,f144,f486])).

fof(f151,plain,
    ( spl6_17
  <=> k1_relset_1(sK0,sK1,sK2) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f472,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl6_14
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f468,f145])).

fof(f468,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_17 ),
    inference(superposition,[],[f152,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',redefinition_k1_relset_1)).

fof(f152,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k1_xboole_0
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f479,plain,
    ( ~ spl6_71
    | ~ spl6_14
    | spl6_19 ),
    inference(avatar_split_clause,[],[f471,f159,f144,f477])).

fof(f477,plain,
    ( spl6_71
  <=> ~ v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f159,plain,
    ( spl6_19
  <=> ~ v1_xboole_0(k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f471,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl6_14
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f466,f160])).

fof(f160,plain,
    ( ~ v1_xboole_0(k1_relset_1(sK0,sK1,sK2))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f159])).

fof(f466,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f145,f77])).

fof(f464,plain,
    ( spl6_68
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f457,f454,f462])).

fof(f462,plain,
    ( spl6_68
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f454,plain,
    ( spl6_66
  <=> k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f457,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_66 ),
    inference(superposition,[],[f70,f455])).

fof(f455,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f454])).

fof(f456,plain,
    ( spl6_66
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f433,f418,f454])).

fof(f418,plain,
    ( spl6_64
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f433,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_64 ),
    inference(unit_resulting_resolution,[],[f419,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',t6_boole)).

fof(f419,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f418])).

fof(f420,plain,
    ( spl6_64
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f405,f127,f418])).

fof(f405,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f70,f349,f73])).

fof(f349,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f128,f70,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',t5_subset)).

fof(f402,plain,
    ( ~ spl6_63
    | spl6_57 ),
    inference(avatar_split_clause,[],[f378,f375,f400])).

fof(f400,plain,
    ( spl6_63
  <=> ~ r2_hidden(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f375,plain,
    ( spl6_57
  <=> ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f378,plain,
    ( ~ r2_hidden(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_57 ),
    inference(unit_resulting_resolution,[],[f376,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',t1_subset)).

fof(f376,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f375])).

fof(f393,plain,
    ( ~ spl6_61
    | spl6_55 ),
    inference(avatar_split_clause,[],[f367,f362,f391])).

fof(f391,plain,
    ( spl6_61
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f362,plain,
    ( spl6_55
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f367,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_55 ),
    inference(unit_resulting_resolution,[],[f363,f72])).

fof(f363,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f362])).

fof(f386,plain,
    ( ~ spl6_59
    | spl6_53 ),
    inference(avatar_split_clause,[],[f365,f355,f384])).

fof(f384,plain,
    ( spl6_59
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f355,plain,
    ( spl6_53
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f365,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_53 ),
    inference(unit_resulting_resolution,[],[f356,f72])).

fof(f356,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f355])).

fof(f377,plain,
    ( ~ spl6_57
    | ~ spl6_10
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f348,f290,f127,f375])).

fof(f290,plain,
    ( spl6_40
  <=> r2_hidden(sK4(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f348,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f291,f128,f82])).

fof(f291,plain,
    ( r2_hidden(sK4(sK5),sK5)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f290])).

fof(f364,plain,
    ( ~ spl6_55
    | ~ spl6_10
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f347,f271,f127,f362])).

fof(f271,plain,
    ( spl6_38
  <=> r2_hidden(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f347,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f272,f128,f82])).

fof(f272,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f271])).

fof(f357,plain,
    ( ~ spl6_53
    | ~ spl6_10
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f346,f264,f127,f355])).

fof(f264,plain,
    ( spl6_36
  <=> r2_hidden(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f346,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f265,f128,f82])).

fof(f265,plain,
    ( r2_hidden(sK4(sK0),sK0)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f264])).

fof(f342,plain,
    ( ~ spl6_51
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f304,f290,f340])).

fof(f340,plain,
    ( spl6_51
  <=> ~ r2_hidden(sK5,sK4(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f304,plain,
    ( ~ r2_hidden(sK5,sK4(sK5))
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f291,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',antisymmetry_r2_hidden)).

fof(f334,plain,
    ( ~ spl6_49
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f205,f198,f332])).

fof(f332,plain,
    ( spl6_49
  <=> ~ r2_hidden(sK5,sK3(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f198,plain,
    ( spl6_24
  <=> r2_hidden(sK3(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f205,plain,
    ( ~ r2_hidden(sK5,sK3(sK5))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f199,f71])).

fof(f199,plain,
    ( r2_hidden(sK3(sK5),sK5)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f198])).

fof(f321,plain,
    ( ~ spl6_47
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f282,f271,f319])).

fof(f319,plain,
    ( spl6_47
  <=> ~ r2_hidden(sK1,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f282,plain,
    ( ~ r2_hidden(sK1,sK4(sK1))
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f272,f71])).

fof(f314,plain,
    ( ~ spl6_45
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f276,f264,f312])).

fof(f312,plain,
    ( spl6_45
  <=> ~ r2_hidden(sK0,sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f276,plain,
    ( ~ r2_hidden(sK0,sK4(sK0))
    | ~ spl6_36 ),
    inference(unit_resulting_resolution,[],[f265,f71])).

fof(f301,plain,
    ( spl6_42
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f294,f144,f299])).

fof(f294,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f145,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',cc1_relset_1)).

fof(f292,plain,
    ( spl6_40
    | spl6_7 ),
    inference(avatar_split_clause,[],[f253,f110,f290])).

fof(f110,plain,
    ( spl6_7
  <=> ~ v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f253,plain,
    ( r2_hidden(sK4(sK5),sK5)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f70,f111,f73])).

fof(f111,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f273,plain,
    ( spl6_38
    | spl6_3 ),
    inference(avatar_split_clause,[],[f251,f96,f271])).

fof(f96,plain,
    ( spl6_3
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f251,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f70,f97,f73])).

fof(f97,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f266,plain,
    ( spl6_36
    | spl6_1 ),
    inference(avatar_split_clause,[],[f249,f89,f264])).

fof(f89,plain,
    ( spl6_1
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f249,plain,
    ( r2_hidden(sK4(sK0),sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f70,f90,f73])).

fof(f90,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f247,plain,
    ( spl6_34
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f203,f198,f245])).

fof(f245,plain,
    ( spl6_34
  <=> m1_subset_1(sK3(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f203,plain,
    ( m1_subset_1(sK3(sK5),sK5)
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f199,f72])).

fof(f236,plain,
    ( spl6_32
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f202,f181,f234])).

fof(f181,plain,
    ( spl6_22
  <=> r2_hidden(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f202,plain,
    ( m1_subset_1(sK3(sK1),sK1)
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f182,f72])).

fof(f182,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f229,plain,
    ( spl6_30
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f201,f174,f227])).

fof(f227,plain,
    ( spl6_30
  <=> m1_subset_1(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f174,plain,
    ( spl6_20
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f201,plain,
    ( m1_subset_1(sK3(sK0),sK0)
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f175,f72])).

fof(f175,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f174])).

fof(f222,plain,
    ( ~ spl6_29
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f190,f181,f220])).

fof(f220,plain,
    ( spl6_29
  <=> ~ r2_hidden(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f190,plain,
    ( ~ r2_hidden(sK1,sK3(sK1))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f182,f71])).

fof(f215,plain,
    ( ~ spl6_27
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f185,f174,f213])).

fof(f213,plain,
    ( spl6_27
  <=> ~ r2_hidden(sK0,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f185,plain,
    ( ~ r2_hidden(sK0,sK3(sK0))
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f175,f71])).

fof(f200,plain,
    ( spl6_24
    | spl6_7 ),
    inference(avatar_split_clause,[],[f165,f110,f198])).

fof(f165,plain,
    ( r2_hidden(sK3(sK5),sK5)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f111,f69])).

fof(f183,plain,
    ( spl6_22
    | spl6_3 ),
    inference(avatar_split_clause,[],[f164,f96,f181])).

fof(f164,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f97,f69])).

fof(f176,plain,
    ( spl6_20
    | spl6_1 ),
    inference(avatar_split_clause,[],[f163,f89,f174])).

fof(f163,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f90,f69])).

fof(f161,plain,
    ( ~ spl6_19
    | spl6_17 ),
    inference(avatar_split_clause,[],[f154,f151,f159])).

fof(f154,plain,
    ( ~ v1_xboole_0(k1_relset_1(sK0,sK1,sK2))
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f152,f67])).

fof(f153,plain,(
    ~ spl6_17 ),
    inference(avatar_split_clause,[],[f62,f151])).

fof(f62,plain,(
    k1_relset_1(sK0,sK1,sK2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

fof(f146,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f61,f144])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f138,plain,
    ( spl6_12
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f120,f103,f136])).

fof(f136,plain,
    ( spl6_12
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f103,plain,
    ( spl6_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f120,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f104,f67])).

fof(f104,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f129,plain,
    ( spl6_10
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f122,f103,f127])).

fof(f122,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f120,f104])).

fof(f119,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f84,f117])).

fof(f117,plain,
    ( spl6_8
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f84,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( v1_relat_1(sK5)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK5)
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f27,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',rc1_relat_1)).

fof(f112,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f83,f110])).

fof(f83,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f105,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f64,f103])).

fof(f64,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t49_relset_1.p',dt_o_0_0_xboole_0)).

fof(f98,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f60,f96])).

fof(f60,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f91,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f59,f89])).

fof(f59,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
