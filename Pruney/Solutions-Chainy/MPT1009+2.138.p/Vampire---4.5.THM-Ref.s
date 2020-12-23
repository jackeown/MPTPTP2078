%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:46 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 316 expanded)
%              Number of leaves         :   33 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          :  376 ( 767 expanded)
%              Number of equality atoms :   93 ( 236 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f337,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f126,f149,f158,f233,f254,f280,f327,f336])).

fof(f336,plain,
    ( ~ spl9_3
    | ~ spl9_5
    | ~ spl9_12 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_12 ),
    inference(resolution,[],[f331,f143])).

fof(f143,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f331,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl9_5
    | ~ spl9_12 ),
    inference(resolution,[],[f330,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f330,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl9_5
    | ~ spl9_12 ),
    inference(backward_demodulation,[],[f207,f329])).

fof(f329,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl9_5
    | ~ spl9_12 ),
    inference(trivial_inequality_removal,[],[f328])).

fof(f328,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl9_5
    | ~ spl9_12 ),
    inference(superposition,[],[f326,f228])).

fof(f228,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl9_5
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f326,plain,
    ( ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
        | k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) )
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl9_12
  <=> ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
        | k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f207,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f92,f206])).

fof(f206,plain,(
    ! [X0] : k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f89,f93])).

fof(f93,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f58,f91])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f92,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f60,f91,f91])).

fof(f60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f327,plain,
    ( ~ spl9_3
    | spl9_12 ),
    inference(avatar_split_clause,[],[f323,f325,f142])).

fof(f323,plain,(
    ! [X0] :
      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
      | k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f95,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f78,f91,f91])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f280,plain,
    ( ~ spl9_2
    | ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(resolution,[],[f264,f61])).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f264,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f261,f177])).

fof(f177,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl9_2 ),
    inference(resolution,[],[f171,f121])).

fof(f121,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl9_2
  <=> ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f163,f101])).

fof(f101,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f85,f61])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f163,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK4(X5),X6)
      | ~ r1_tarski(X5,X6)
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f135,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f135,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(sK4(X0),X1) ) ),
    inference(resolution,[],[f79,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f261,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl9_9 ),
    inference(backward_demodulation,[],[f207,f253])).

fof(f253,plain,
    ( k1_xboole_0 = sK3
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl9_9
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f254,plain,
    ( ~ spl9_3
    | spl9_9
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f240,f230,f251,f142])).

fof(f230,plain,
    ( spl9_6
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f240,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl9_6 ),
    inference(trivial_inequality_removal,[],[f239])).

fof(f239,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl9_6 ),
    inference(superposition,[],[f65,f232])).

fof(f232,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f230])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f233,plain,
    ( spl9_5
    | spl9_6
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f224,f146,f230,f226])).

fof(f146,plain,
    ( spl9_4
  <=> r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f224,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl9_4 ),
    inference(resolution,[],[f98,f148])).

fof(f148,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f146])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f82,f91,f91])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f158,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl9_3 ),
    inference(resolution,[],[f153,f73])).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f153,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | spl9_3 ),
    inference(resolution,[],[f150,f93])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl9_3 ),
    inference(resolution,[],[f144,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f144,plain,
    ( ~ v1_relat_1(sK3)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f149,plain,
    ( ~ spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f140,f146,f142])).

fof(f140,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f139,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f139,plain,(
    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f87,f93])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f126,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl9_1 ),
    inference(resolution,[],[f124,f101])).

fof(f124,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | spl9_1 ),
    inference(resolution,[],[f118,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK5(X0)
          & r2_hidden(sK5(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK6(X4),sK7(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f45,f47,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK5(X0)
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK6(X4),sK7(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f118,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f122,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f114,f120,f116])).

fof(f114,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f75,f108])).

fof(f108,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f104,f63])).

fof(f104,plain,(
    v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f102,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f102,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f101,f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:04:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.17/0.52  % (5039)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.17/0.52  % (5020)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.52  % (5015)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.17/0.52  % (5016)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.17/0.53  % (5031)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.53  % (5024)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.53  % (5038)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.53  % (5019)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  % (5017)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.53  % (5021)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.54  % (5030)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.54  % (5044)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.54  % (5017)Refutation not found, incomplete strategy% (5017)------------------------------
% 1.29/0.54  % (5017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (5017)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (5017)Memory used [KB]: 10746
% 1.29/0.54  % (5017)Time elapsed: 0.126 s
% 1.29/0.54  % (5017)------------------------------
% 1.29/0.54  % (5017)------------------------------
% 1.29/0.54  % (5042)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.54  % (5037)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.54  % (5018)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.54  % (5022)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.54  % (5043)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.54  % (5037)Refutation not found, incomplete strategy% (5037)------------------------------
% 1.29/0.54  % (5037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (5037)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (5037)Memory used [KB]: 10746
% 1.29/0.54  % (5037)Time elapsed: 0.139 s
% 1.29/0.54  % (5037)------------------------------
% 1.29/0.54  % (5037)------------------------------
% 1.29/0.55  % (5041)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.55  % (5035)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.55  % (5033)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.55  % (5023)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.55  % (5036)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.55  % (5028)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.55  % (5034)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.55  % (5026)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.55  % (5026)Refutation not found, incomplete strategy% (5026)------------------------------
% 1.29/0.55  % (5026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (5026)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (5026)Memory used [KB]: 10618
% 1.29/0.55  % (5026)Time elapsed: 0.149 s
% 1.29/0.55  % (5026)------------------------------
% 1.29/0.55  % (5026)------------------------------
% 1.29/0.55  % (5029)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.56  % (5027)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.56  % (5023)Refutation not found, incomplete strategy% (5023)------------------------------
% 1.29/0.56  % (5023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (5023)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (5023)Memory used [KB]: 10746
% 1.29/0.56  % (5023)Time elapsed: 0.154 s
% 1.29/0.56  % (5023)------------------------------
% 1.29/0.56  % (5023)------------------------------
% 1.29/0.56  % (5027)Refutation found. Thanks to Tanya!
% 1.29/0.56  % SZS status Theorem for theBenchmark
% 1.29/0.56  % SZS output start Proof for theBenchmark
% 1.29/0.56  fof(f337,plain,(
% 1.29/0.56    $false),
% 1.29/0.56    inference(avatar_sat_refutation,[],[f122,f126,f149,f158,f233,f254,f280,f327,f336])).
% 1.29/0.56  fof(f336,plain,(
% 1.29/0.56    ~spl9_3 | ~spl9_5 | ~spl9_12),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f332])).
% 1.29/0.56  fof(f332,plain,(
% 1.29/0.56    $false | (~spl9_3 | ~spl9_5 | ~spl9_12)),
% 1.29/0.56    inference(resolution,[],[f331,f143])).
% 1.29/0.56  fof(f143,plain,(
% 1.29/0.56    v1_relat_1(sK3) | ~spl9_3),
% 1.29/0.56    inference(avatar_component_clause,[],[f142])).
% 1.29/0.56  fof(f142,plain,(
% 1.29/0.56    spl9_3 <=> v1_relat_1(sK3)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.29/0.56  fof(f331,plain,(
% 1.29/0.56    ~v1_relat_1(sK3) | (~spl9_5 | ~spl9_12)),
% 1.29/0.56    inference(resolution,[],[f330,f75])).
% 1.29/0.56  fof(f75,plain,(
% 1.29/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f30])).
% 1.29/0.56  fof(f30,plain,(
% 1.29/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.29/0.56    inference(ennf_transformation,[],[f14])).
% 1.29/0.56  fof(f14,axiom,(
% 1.29/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.29/0.56  fof(f330,plain,(
% 1.29/0.56    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (~spl9_5 | ~spl9_12)),
% 1.29/0.56    inference(backward_demodulation,[],[f207,f329])).
% 1.29/0.56  fof(f329,plain,(
% 1.29/0.56    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl9_5 | ~spl9_12)),
% 1.29/0.56    inference(trivial_inequality_removal,[],[f328])).
% 1.29/0.56  fof(f328,plain,(
% 1.29/0.56    k1_relat_1(sK3) != k1_relat_1(sK3) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl9_5 | ~spl9_12)),
% 1.29/0.56    inference(superposition,[],[f326,f228])).
% 1.29/0.56  fof(f228,plain,(
% 1.29/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl9_5),
% 1.29/0.56    inference(avatar_component_clause,[],[f226])).
% 1.29/0.56  fof(f226,plain,(
% 1.29/0.56    spl9_5 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.29/0.56  fof(f326,plain,(
% 1.29/0.56    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0))) ) | ~spl9_12),
% 1.29/0.56    inference(avatar_component_clause,[],[f325])).
% 1.29/0.56  fof(f325,plain,(
% 1.29/0.56    spl9_12 <=> ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)))),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.29/0.56  fof(f207,plain,(
% 1.29/0.56    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.29/0.56    inference(backward_demodulation,[],[f92,f206])).
% 1.29/0.56  fof(f206,plain,(
% 1.29/0.56    ( ! [X0] : (k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.29/0.56    inference(resolution,[],[f89,f93])).
% 1.29/0.56  fof(f93,plain,(
% 1.29/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.29/0.56    inference(definition_unfolding,[],[f58,f91])).
% 1.29/0.56  fof(f91,plain,(
% 1.29/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.29/0.56    inference(definition_unfolding,[],[f62,f90])).
% 1.29/0.56  fof(f90,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.29/0.56    inference(definition_unfolding,[],[f74,f86])).
% 1.29/0.56  fof(f86,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f7])).
% 1.29/0.56  fof(f7,axiom,(
% 1.29/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.29/0.56  fof(f74,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f6])).
% 1.29/0.56  fof(f6,axiom,(
% 1.29/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.29/0.56  fof(f62,plain,(
% 1.29/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f5])).
% 1.29/0.56  fof(f5,axiom,(
% 1.29/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.29/0.56  fof(f58,plain,(
% 1.29/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.29/0.56    inference(cnf_transformation,[],[f39])).
% 1.29/0.56  fof(f39,plain,(
% 1.29/0.56    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 1.29/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f38])).
% 1.29/0.56  fof(f38,plain,(
% 1.29/0.56    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f23,plain,(
% 1.29/0.56    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.29/0.56    inference(flattening,[],[f22])).
% 1.29/0.56  fof(f22,plain,(
% 1.29/0.56    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.29/0.56    inference(ennf_transformation,[],[f21])).
% 1.29/0.56  fof(f21,negated_conjecture,(
% 1.29/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.29/0.56    inference(negated_conjecture,[],[f20])).
% 1.29/0.56  fof(f20,conjecture,(
% 1.29/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.29/0.56  fof(f89,plain,(
% 1.29/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f37])).
% 1.29/0.56  fof(f37,plain,(
% 1.29/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.56    inference(ennf_transformation,[],[f19])).
% 1.29/0.56  fof(f19,axiom,(
% 1.29/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.29/0.56  fof(f92,plain,(
% 1.29/0.56    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.29/0.56    inference(definition_unfolding,[],[f60,f91,f91])).
% 1.29/0.56  fof(f60,plain,(
% 1.29/0.56    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.29/0.56    inference(cnf_transformation,[],[f39])).
% 1.29/0.56  fof(f327,plain,(
% 1.29/0.56    ~spl9_3 | spl9_12),
% 1.29/0.56    inference(avatar_split_clause,[],[f323,f325,f142])).
% 1.29/0.56  fof(f323,plain,(
% 1.29/0.56    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 1.29/0.56    inference(resolution,[],[f95,f56])).
% 1.29/0.56  fof(f56,plain,(
% 1.29/0.56    v1_funct_1(sK3)),
% 1.29/0.56    inference(cnf_transformation,[],[f39])).
% 1.29/0.56  fof(f95,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.29/0.56    inference(definition_unfolding,[],[f78,f91,f91])).
% 1.29/0.56  fof(f78,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f33])).
% 1.29/0.56  fof(f33,plain,(
% 1.29/0.56    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.29/0.56    inference(flattening,[],[f32])).
% 1.29/0.56  fof(f32,plain,(
% 1.29/0.56    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.29/0.56    inference(ennf_transformation,[],[f16])).
% 1.29/0.56  fof(f16,axiom,(
% 1.29/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.29/0.56  fof(f280,plain,(
% 1.29/0.56    ~spl9_2 | ~spl9_9),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f279])).
% 1.29/0.56  fof(f279,plain,(
% 1.29/0.56    $false | (~spl9_2 | ~spl9_9)),
% 1.29/0.56    inference(resolution,[],[f264,f61])).
% 1.29/0.56  fof(f61,plain,(
% 1.29/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f4])).
% 1.29/0.56  fof(f4,axiom,(
% 1.29/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.29/0.56  fof(f264,plain,(
% 1.29/0.56    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | (~spl9_2 | ~spl9_9)),
% 1.29/0.56    inference(forward_demodulation,[],[f261,f177])).
% 1.29/0.56  fof(f177,plain,(
% 1.29/0.56    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl9_2),
% 1.29/0.56    inference(resolution,[],[f171,f121])).
% 1.29/0.56  fof(f121,plain,(
% 1.29/0.56    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl9_2),
% 1.29/0.56    inference(avatar_component_clause,[],[f120])).
% 1.29/0.56  fof(f120,plain,(
% 1.29/0.56    spl9_2 <=> ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.29/0.56  fof(f171,plain,(
% 1.29/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.29/0.56    inference(resolution,[],[f163,f101])).
% 1.29/0.56  fof(f101,plain,(
% 1.29/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.29/0.56    inference(resolution,[],[f85,f61])).
% 1.29/0.56  fof(f85,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f35])).
% 1.29/0.56  fof(f35,plain,(
% 1.29/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.29/0.56    inference(ennf_transformation,[],[f17])).
% 1.29/0.56  fof(f17,axiom,(
% 1.29/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.29/0.56  fof(f163,plain,(
% 1.29/0.56    ( ! [X6,X5] : (r2_hidden(sK4(X5),X6) | ~r1_tarski(X5,X6) | k1_xboole_0 = X5) )),
% 1.29/0.56    inference(resolution,[],[f135,f63])).
% 1.29/0.56  fof(f63,plain,(
% 1.29/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.29/0.56    inference(cnf_transformation,[],[f24])).
% 1.29/0.56  fof(f24,plain,(
% 1.29/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f3])).
% 1.29/0.56  fof(f3,axiom,(
% 1.29/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.29/0.56  fof(f135,plain,(
% 1.29/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r1_tarski(X0,X1) | r2_hidden(sK4(X0),X1)) )),
% 1.29/0.56    inference(resolution,[],[f79,f69])).
% 1.29/0.56  fof(f69,plain,(
% 1.29/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f43])).
% 1.29/0.56  fof(f43,plain,(
% 1.29/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).
% 1.29/0.56  fof(f42,plain,(
% 1.29/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f41,plain,(
% 1.29/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.56    inference(rectify,[],[f40])).
% 1.29/0.56  fof(f40,plain,(
% 1.29/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.29/0.56    inference(nnf_transformation,[],[f1])).
% 1.29/0.56  fof(f1,axiom,(
% 1.29/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.29/0.56  fof(f79,plain,(
% 1.29/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f53])).
% 1.29/0.56  fof(f53,plain,(
% 1.29/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.29/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).
% 1.29/0.56  fof(f52,plain,(
% 1.29/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f51,plain,(
% 1.29/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.29/0.56    inference(rectify,[],[f50])).
% 1.29/0.56  fof(f50,plain,(
% 1.29/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.29/0.56    inference(nnf_transformation,[],[f34])).
% 1.29/0.56  fof(f34,plain,(
% 1.29/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f2])).
% 1.29/0.56  fof(f2,axiom,(
% 1.29/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.29/0.56  fof(f261,plain,(
% 1.29/0.56    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) | ~spl9_9),
% 1.29/0.56    inference(backward_demodulation,[],[f207,f253])).
% 1.29/0.56  fof(f253,plain,(
% 1.29/0.56    k1_xboole_0 = sK3 | ~spl9_9),
% 1.29/0.56    inference(avatar_component_clause,[],[f251])).
% 1.29/0.56  fof(f251,plain,(
% 1.29/0.56    spl9_9 <=> k1_xboole_0 = sK3),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.29/0.56  fof(f254,plain,(
% 1.29/0.56    ~spl9_3 | spl9_9 | ~spl9_6),
% 1.29/0.56    inference(avatar_split_clause,[],[f240,f230,f251,f142])).
% 1.29/0.56  fof(f230,plain,(
% 1.29/0.56    spl9_6 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.29/0.56  fof(f240,plain,(
% 1.29/0.56    k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl9_6),
% 1.29/0.56    inference(trivial_inequality_removal,[],[f239])).
% 1.29/0.56  fof(f239,plain,(
% 1.29/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl9_6),
% 1.29/0.56    inference(superposition,[],[f65,f232])).
% 1.29/0.56  fof(f232,plain,(
% 1.29/0.56    k1_xboole_0 = k1_relat_1(sK3) | ~spl9_6),
% 1.29/0.56    inference(avatar_component_clause,[],[f230])).
% 1.29/0.56  fof(f65,plain,(
% 1.29/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f27])).
% 1.29/0.56  fof(f27,plain,(
% 1.29/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.29/0.56    inference(flattening,[],[f26])).
% 1.29/0.56  fof(f26,plain,(
% 1.29/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f15])).
% 1.29/0.56  fof(f15,axiom,(
% 1.29/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.29/0.56  fof(f233,plain,(
% 1.29/0.56    spl9_5 | spl9_6 | ~spl9_4),
% 1.29/0.56    inference(avatar_split_clause,[],[f224,f146,f230,f226])).
% 1.29/0.56  fof(f146,plain,(
% 1.29/0.56    spl9_4 <=> r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.29/0.56  fof(f224,plain,(
% 1.29/0.56    k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl9_4),
% 1.29/0.56    inference(resolution,[],[f98,f148])).
% 1.29/0.56  fof(f148,plain,(
% 1.29/0.56    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl9_4),
% 1.29/0.56    inference(avatar_component_clause,[],[f146])).
% 1.29/0.56  fof(f98,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.29/0.56    inference(definition_unfolding,[],[f82,f91,f91])).
% 1.29/0.56  fof(f82,plain,(
% 1.29/0.56    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f55])).
% 1.29/0.56  fof(f55,plain,(
% 1.29/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.29/0.56    inference(flattening,[],[f54])).
% 1.29/0.56  fof(f54,plain,(
% 1.29/0.56    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.29/0.56    inference(nnf_transformation,[],[f8])).
% 1.29/0.56  fof(f8,axiom,(
% 1.29/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.29/0.56  fof(f158,plain,(
% 1.29/0.56    spl9_3),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f155])).
% 1.29/0.56  fof(f155,plain,(
% 1.29/0.56    $false | spl9_3),
% 1.29/0.56    inference(resolution,[],[f153,f73])).
% 1.29/0.56  fof(f73,plain,(
% 1.29/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f13])).
% 1.29/0.56  fof(f13,axiom,(
% 1.29/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.29/0.56  fof(f153,plain,(
% 1.29/0.56    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | spl9_3),
% 1.29/0.56    inference(resolution,[],[f150,f93])).
% 1.29/0.56  fof(f150,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl9_3),
% 1.29/0.56    inference(resolution,[],[f144,f67])).
% 1.29/0.56  fof(f67,plain,(
% 1.29/0.56    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f28])).
% 1.29/0.56  fof(f28,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f9])).
% 1.29/0.56  fof(f9,axiom,(
% 1.29/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.29/0.56  fof(f144,plain,(
% 1.29/0.56    ~v1_relat_1(sK3) | spl9_3),
% 1.29/0.56    inference(avatar_component_clause,[],[f142])).
% 1.29/0.56  fof(f149,plain,(
% 1.29/0.56    ~spl9_3 | spl9_4),
% 1.29/0.56    inference(avatar_split_clause,[],[f140,f146,f142])).
% 1.29/0.56  fof(f140,plain,(
% 1.29/0.56    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_relat_1(sK3)),
% 1.29/0.56    inference(resolution,[],[f139,f76])).
% 1.29/0.56  fof(f76,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f49])).
% 1.29/0.56  fof(f49,plain,(
% 1.29/0.56    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.29/0.56    inference(nnf_transformation,[],[f31])).
% 1.29/0.56  fof(f31,plain,(
% 1.29/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.29/0.56    inference(ennf_transformation,[],[f10])).
% 1.29/0.56  fof(f10,axiom,(
% 1.29/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.29/0.56  fof(f139,plain,(
% 1.29/0.56    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.29/0.56    inference(resolution,[],[f87,f93])).
% 1.29/0.56  fof(f87,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f36])).
% 1.29/0.56  fof(f36,plain,(
% 1.29/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.29/0.56    inference(ennf_transformation,[],[f18])).
% 1.29/0.56  fof(f18,axiom,(
% 1.29/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.29/0.56  fof(f126,plain,(
% 1.29/0.56    spl9_1),
% 1.29/0.56    inference(avatar_contradiction_clause,[],[f125])).
% 1.29/0.56  fof(f125,plain,(
% 1.29/0.56    $false | spl9_1),
% 1.29/0.56    inference(resolution,[],[f124,f101])).
% 1.29/0.56  fof(f124,plain,(
% 1.29/0.56    r2_hidden(sK5(k1_xboole_0),k1_xboole_0) | spl9_1),
% 1.29/0.56    inference(resolution,[],[f118,f71])).
% 1.29/0.56  fof(f71,plain,(
% 1.29/0.56    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK5(X0),X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f48])).
% 1.29/0.56  fof(f48,plain,(
% 1.29/0.56    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK5(X0) & r2_hidden(sK5(X0),X0))) & (! [X4] : (k4_tarski(sK6(X4),sK7(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.29/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f45,f47,f46])).
% 1.29/0.56  fof(f46,plain,(
% 1.29/0.56    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK5(X0) & r2_hidden(sK5(X0),X0)))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f47,plain,(
% 1.29/0.56    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK6(X4),sK7(X4)) = X4)),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f45,plain,(
% 1.29/0.56    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.29/0.56    inference(rectify,[],[f44])).
% 1.29/0.56  fof(f44,plain,(
% 1.29/0.56    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.29/0.56    inference(nnf_transformation,[],[f29])).
% 1.29/0.56  fof(f29,plain,(
% 1.29/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f11])).
% 1.29/0.56  fof(f11,axiom,(
% 1.29/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.29/0.56  fof(f118,plain,(
% 1.29/0.56    ~v1_relat_1(k1_xboole_0) | spl9_1),
% 1.29/0.56    inference(avatar_component_clause,[],[f116])).
% 1.29/0.56  fof(f116,plain,(
% 1.29/0.56    spl9_1 <=> v1_relat_1(k1_xboole_0)),
% 1.29/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.29/0.56  fof(f122,plain,(
% 1.29/0.56    ~spl9_1 | spl9_2),
% 1.29/0.56    inference(avatar_split_clause,[],[f114,f120,f116])).
% 1.29/0.56  fof(f114,plain,(
% 1.29/0.56    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.29/0.56    inference(superposition,[],[f75,f108])).
% 1.29/0.56  fof(f108,plain,(
% 1.29/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.29/0.56    inference(resolution,[],[f104,f63])).
% 1.29/0.56  fof(f104,plain,(
% 1.29/0.56    v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 1.29/0.56    inference(resolution,[],[f102,f64])).
% 1.29/0.56  fof(f64,plain,(
% 1.29/0.56    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0))) )),
% 1.29/0.56    inference(cnf_transformation,[],[f25])).
% 1.29/0.56  fof(f25,plain,(
% 1.29/0.56    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f12])).
% 1.29/0.56  fof(f12,axiom,(
% 1.29/0.56    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 1.29/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 1.29/0.56  fof(f102,plain,(
% 1.29/0.56    v1_xboole_0(k1_xboole_0)),
% 1.29/0.56    inference(resolution,[],[f101,f69])).
% 1.29/0.56  % SZS output end Proof for theBenchmark
% 1.29/0.56  % (5027)------------------------------
% 1.29/0.56  % (5027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (5027)Termination reason: Refutation
% 1.29/0.56  
% 1.29/0.56  % (5027)Memory used [KB]: 6268
% 1.29/0.56  % (5027)Time elapsed: 0.154 s
% 1.29/0.56  % (5027)------------------------------
% 1.29/0.56  % (5027)------------------------------
% 1.29/0.56  % (5014)Success in time 0.197 s
%------------------------------------------------------------------------------
