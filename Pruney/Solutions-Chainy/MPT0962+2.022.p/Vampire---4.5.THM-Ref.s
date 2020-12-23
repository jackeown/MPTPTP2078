%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:24 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 587 expanded)
%              Number of leaves         :   23 ( 157 expanded)
%              Depth                    :   20
%              Number of atoms          :  503 (2428 expanded)
%              Number of equality atoms :   94 ( 699 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f82,f110,f136,f157,f174,f175,f222,f234,f298,f301,f313])).

fof(f313,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f311,f282])).

fof(f282,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f239,f279])).

fof(f279,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f276,f239])).

fof(f276,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(resolution,[],[f275,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f275,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
        | k1_xboole_0 = X0
        | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f265,f60])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
        | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | k1_xboole_0 = X0
        | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(resolution,[],[f256,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f256,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),X1)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f250,f221])).

fof(f221,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl3_16
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X1)
        | ~ r1_tarski(k1_xboole_0,X0)
        | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f231,f221])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k1_relat_1(sK1),X1) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f225,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f225,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k1_relat_1(sK1),X1)
        | ~ v1_relat_1(sK1) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(superposition,[],[f51,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f94,f177])).

fof(f177,plain,
    ( k1_xboole_0 = sK0
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f176,f75])).

fof(f75,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f176,plain,
    ( k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f168,f169])).

fof(f169,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f78,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f168,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_5
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f239,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f179,f221])).

fof(f179,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f75,f177])).

fof(f311,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f310,f221])).

fof(f310,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f129,f177])).

fof(f129,plain,
    ( v1_funct_2(sK1,k1_xboole_0,sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_10
  <=> v1_funct_2(sK1,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f301,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_11
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_11
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f288,f38])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f288,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_11
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f261,f279])).

fof(f261,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | spl3_11
    | ~ spl3_16 ),
    inference(resolution,[],[f238,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f238,plain,
    ( r2_hidden(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),k1_relat_1(k1_xboole_0))
    | spl3_11
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f166,f221])).

fof(f166,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),k1_xboole_0),k1_relat_1(sK1))
    | spl3_11 ),
    inference(resolution,[],[f134,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

% (13075)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f134,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_11
  <=> r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f298,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_9
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_9
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f283,f241])).

fof(f241,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | spl3_9
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f187,f221])).

fof(f187,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | spl3_2
    | ~ spl3_3
    | spl3_9 ),
    inference(backward_demodulation,[],[f125,f177])).

fof(f125,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_9
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f283,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f243,f279])).

fof(f243,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f189,f221])).

fof(f189,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)
    | spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f169,f177])).

fof(f234,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl3_15 ),
    inference(subsumption_resolution,[],[f232,f38])).

fof(f232,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_15 ),
    inference(resolution,[],[f224,f39])).

fof(f224,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK1),k1_xboole_0)
    | spl3_15 ),
    inference(resolution,[],[f217,f44])).

fof(f217,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl3_15
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f222,plain,
    ( ~ spl3_15
    | spl3_16
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f213,f77,f73,f219,f215])).

fof(f213,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(k1_xboole_0,sK1)
    | spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f204,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f204,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f190,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f190,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))
    | spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f170,f177])).

fof(f170,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f78,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f175,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f164,f92,f88])).

fof(f88,plain,
    ( spl3_4
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f164,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f36,f42])).

fof(f36,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f174,plain,
    ( spl3_2
    | ~ spl3_3
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | spl3_6 ),
    inference(subsumption_resolution,[],[f169,f172])).

fof(f172,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | spl3_2
    | ~ spl3_3
    | spl3_6 ),
    inference(subsumption_resolution,[],[f171,f75])).

fof(f171,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl3_3
    | spl3_6 ),
    inference(subsumption_resolution,[],[f168,f113])).

fof(f113,plain,
    ( k1_xboole_0 != sK0
    | spl3_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f157,plain,
    ( spl3_4
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f149,f38])).

fof(f149,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_4
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f97,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f97,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_4 ),
    inference(resolution,[],[f96,f39])).

fof(f96,plain,
    ( r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0)
    | spl3_4 ),
    inference(resolution,[],[f90,f44])).

fof(f90,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f136,plain,
    ( spl3_10
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f106,f132,f124,f128])).

fof(f106,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1)
    | v1_funct_2(sK1,k1_xboole_0,sK0) ),
    inference(resolution,[],[f86,f66])).

fof(f66,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(subsumption_resolution,[],[f83,f34])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ r1_tarski(k1_relat_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f36,f51])).

fof(f110,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f101,f60])).

fof(f101,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | spl3_3 ),
    inference(resolution,[],[f86,f79])).

fof(f79,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f82,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f71,f35])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f37,f77,f73,f69])).

fof(f37,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:11:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (13078)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (13092)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (13074)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (13074)Refutation not found, incomplete strategy% (13074)------------------------------
% 0.22/0.54  % (13074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13092)Refutation not found, incomplete strategy% (13092)------------------------------
% 0.22/0.54  % (13092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13074)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13074)Memory used [KB]: 6268
% 0.22/0.54  % (13074)Time elapsed: 0.117 s
% 0.22/0.54  % (13074)------------------------------
% 0.22/0.54  % (13074)------------------------------
% 0.22/0.55  % (13092)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13092)Memory used [KB]: 10746
% 0.22/0.55  % (13092)Time elapsed: 0.117 s
% 0.22/0.55  % (13092)------------------------------
% 0.22/0.55  % (13092)------------------------------
% 0.22/0.55  % (13070)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.46/0.55  % (13085)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.46/0.56  % (13078)Refutation found. Thanks to Tanya!
% 1.46/0.56  % SZS status Theorem for theBenchmark
% 1.46/0.56  % SZS output start Proof for theBenchmark
% 1.46/0.56  fof(f316,plain,(
% 1.46/0.56    $false),
% 1.46/0.56    inference(avatar_sat_refutation,[],[f80,f82,f110,f136,f157,f174,f175,f222,f234,f298,f301,f313])).
% 1.46/0.56  fof(f313,plain,(
% 1.46/0.56    spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_16),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f312])).
% 1.46/0.56  fof(f312,plain,(
% 1.46/0.56    $false | (spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_10 | ~spl3_16)),
% 1.46/0.56    inference(subsumption_resolution,[],[f311,f282])).
% 1.46/0.56  fof(f282,plain,(
% 1.46/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_16)),
% 1.46/0.56    inference(backward_demodulation,[],[f239,f279])).
% 1.46/0.56  fof(f279,plain,(
% 1.46/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_16)),
% 1.46/0.56    inference(subsumption_resolution,[],[f276,f239])).
% 1.46/0.56  fof(f276,plain,(
% 1.46/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_16)),
% 1.46/0.56    inference(resolution,[],[f275,f60])).
% 1.46/0.56  fof(f60,plain,(
% 1.46/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.46/0.56    inference(equality_resolution,[],[f40])).
% 1.46/0.56  fof(f40,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.46/0.56    inference(cnf_transformation,[],[f25])).
% 1.46/0.56  fof(f25,plain,(
% 1.46/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.56    inference(flattening,[],[f24])).
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.56    inference(nnf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.56  fof(f275,plain,(
% 1.46/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) ) | (spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_16)),
% 1.46/0.56    inference(subsumption_resolution,[],[f265,f60])).
% 1.46/0.56  fof(f265,plain,(
% 1.46/0.56    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) ) | (spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_16)),
% 1.46/0.56    inference(resolution,[],[f256,f64])).
% 1.46/0.56  fof(f64,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.46/0.56    inference(equality_resolution,[],[f63])).
% 1.46/0.56  fof(f63,plain,(
% 1.46/0.56    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.46/0.56    inference(equality_resolution,[],[f58])).
% 1.46/0.56  fof(f58,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f33])).
% 1.46/0.56  fof(f33,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(nnf_transformation,[],[f21])).
% 1.46/0.56  fof(f21,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(flattening,[],[f20])).
% 1.46/0.56  fof(f20,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f9])).
% 1.46/0.56  fof(f9,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.46/0.56  fof(f256,plain,(
% 1.46/0.56    ( ! [X0,X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(k1_xboole_0),X1) | ~r1_tarski(k1_xboole_0,X0)) ) | (spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_16)),
% 1.46/0.56    inference(forward_demodulation,[],[f250,f221])).
% 1.46/0.56  fof(f221,plain,(
% 1.46/0.56    k1_xboole_0 = sK1 | ~spl3_16),
% 1.46/0.56    inference(avatar_component_clause,[],[f219])).
% 1.46/0.56  fof(f219,plain,(
% 1.46/0.56    spl3_16 <=> k1_xboole_0 = sK1),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.46/0.56  fof(f250,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k1_xboole_0),X1) | ~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_16)),
% 1.46/0.56    inference(backward_demodulation,[],[f231,f221])).
% 1.46/0.56  fof(f231,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(sK1),X1)) ) | (spl3_2 | ~spl3_3 | ~spl3_5)),
% 1.46/0.56    inference(subsumption_resolution,[],[f225,f34])).
% 1.46/0.56  fof(f34,plain,(
% 1.46/0.56    v1_relat_1(sK1)),
% 1.46/0.56    inference(cnf_transformation,[],[f23])).
% 1.46/0.56  fof(f23,plain,(
% 1.46/0.56    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22])).
% 1.46/0.56  fof(f22,plain,(
% 1.46/0.56    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f14,plain,(
% 1.46/0.56    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.46/0.56    inference(flattening,[],[f13])).
% 1.46/0.56  fof(f13,plain,(
% 1.46/0.56    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.46/0.56    inference(ennf_transformation,[],[f11])).
% 1.46/0.56  fof(f11,negated_conjecture,(
% 1.46/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.46/0.56    inference(negated_conjecture,[],[f10])).
% 1.46/0.56  fof(f10,conjecture,(
% 1.46/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.46/0.56  fof(f225,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(sK1),X1) | ~v1_relat_1(sK1)) ) | (spl3_2 | ~spl3_3 | ~spl3_5)),
% 1.46/0.56    inference(superposition,[],[f51,f205])).
% 1.46/0.56  fof(f205,plain,(
% 1.46/0.56    k1_xboole_0 = k2_relat_1(sK1) | (spl3_2 | ~spl3_3 | ~spl3_5)),
% 1.46/0.56    inference(forward_demodulation,[],[f94,f177])).
% 1.46/0.56  fof(f177,plain,(
% 1.46/0.56    k1_xboole_0 = sK0 | (spl3_2 | ~spl3_3)),
% 1.46/0.56    inference(subsumption_resolution,[],[f176,f75])).
% 1.46/0.56  fof(f75,plain,(
% 1.46/0.56    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl3_2),
% 1.46/0.56    inference(avatar_component_clause,[],[f73])).
% 1.46/0.56  fof(f73,plain,(
% 1.46/0.56    spl3_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.46/0.56  fof(f176,plain,(
% 1.46/0.56    k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl3_3),
% 1.46/0.56    inference(subsumption_resolution,[],[f168,f169])).
% 1.46/0.56  fof(f169,plain,(
% 1.46/0.56    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl3_3),
% 1.46/0.56    inference(resolution,[],[f78,f52])).
% 1.46/0.56  fof(f52,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f19])).
% 1.46/0.56  fof(f19,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f7])).
% 1.46/0.56  fof(f7,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.46/0.56  fof(f78,plain,(
% 1.46/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl3_3),
% 1.46/0.56    inference(avatar_component_clause,[],[f77])).
% 1.46/0.56  fof(f77,plain,(
% 1.46/0.56    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.46/0.56  fof(f168,plain,(
% 1.46/0.56    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl3_3),
% 1.46/0.56    inference(resolution,[],[f78,f55])).
% 1.46/0.56  fof(f55,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f33])).
% 1.46/0.56  fof(f94,plain,(
% 1.46/0.56    sK0 = k2_relat_1(sK1) | ~spl3_5),
% 1.46/0.56    inference(avatar_component_clause,[],[f92])).
% 1.46/0.56  fof(f92,plain,(
% 1.46/0.56    spl3_5 <=> sK0 = k2_relat_1(sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.46/0.56  fof(f51,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  fof(f18,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.46/0.56    inference(flattening,[],[f17])).
% 1.46/0.56  fof(f17,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.46/0.56    inference(ennf_transformation,[],[f8])).
% 1.46/0.56  fof(f8,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.46/0.56  fof(f239,plain,(
% 1.46/0.56    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_16)),
% 1.46/0.56    inference(backward_demodulation,[],[f179,f221])).
% 1.46/0.56  fof(f179,plain,(
% 1.46/0.56    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl3_2 | ~spl3_3)),
% 1.46/0.56    inference(backward_demodulation,[],[f75,f177])).
% 1.46/0.56  fof(f311,plain,(
% 1.46/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_10 | ~spl3_16)),
% 1.46/0.56    inference(forward_demodulation,[],[f310,f221])).
% 1.46/0.56  fof(f310,plain,(
% 1.46/0.56    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_10)),
% 1.46/0.56    inference(forward_demodulation,[],[f129,f177])).
% 1.46/0.56  fof(f129,plain,(
% 1.46/0.56    v1_funct_2(sK1,k1_xboole_0,sK0) | ~spl3_10),
% 1.46/0.56    inference(avatar_component_clause,[],[f128])).
% 1.46/0.56  fof(f128,plain,(
% 1.46/0.56    spl3_10 <=> v1_funct_2(sK1,k1_xboole_0,sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.46/0.56  fof(f301,plain,(
% 1.46/0.56    spl3_2 | ~spl3_3 | ~spl3_5 | spl3_11 | ~spl3_16),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f300])).
% 1.46/0.56  fof(f300,plain,(
% 1.46/0.56    $false | (spl3_2 | ~spl3_3 | ~spl3_5 | spl3_11 | ~spl3_16)),
% 1.46/0.56    inference(subsumption_resolution,[],[f288,f38])).
% 1.46/0.56  fof(f38,plain,(
% 1.46/0.56    v1_xboole_0(k1_xboole_0)),
% 1.46/0.56    inference(cnf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    v1_xboole_0(k1_xboole_0)),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.46/0.56  fof(f288,plain,(
% 1.46/0.56    ~v1_xboole_0(k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_5 | spl3_11 | ~spl3_16)),
% 1.46/0.56    inference(backward_demodulation,[],[f261,f279])).
% 1.46/0.56  fof(f261,plain,(
% 1.46/0.56    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | (spl3_11 | ~spl3_16)),
% 1.46/0.56    inference(resolution,[],[f238,f39])).
% 1.46/0.56  fof(f39,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f15])).
% 1.46/0.56  fof(f15,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f12])).
% 1.46/0.56  fof(f12,plain,(
% 1.46/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.46/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.46/0.56  fof(f238,plain,(
% 1.46/0.56    r2_hidden(sK2(k1_relat_1(k1_xboole_0),k1_xboole_0),k1_relat_1(k1_xboole_0)) | (spl3_11 | ~spl3_16)),
% 1.46/0.56    inference(backward_demodulation,[],[f166,f221])).
% 1.46/0.56  fof(f166,plain,(
% 1.46/0.56    r2_hidden(sK2(k1_relat_1(sK1),k1_xboole_0),k1_relat_1(sK1)) | spl3_11),
% 1.46/0.56    inference(resolution,[],[f134,f44])).
% 1.46/0.56  fof(f44,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f29])).
% 1.46/0.56  fof(f29,plain,(
% 1.46/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 1.46/0.56  fof(f28,plain,(
% 1.46/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f27,plain,(
% 1.46/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.46/0.56    inference(rectify,[],[f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.46/0.56    inference(nnf_transformation,[],[f16])).
% 1.46/0.56  fof(f16,plain,(
% 1.46/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f2])).
% 1.46/0.56  % (13075)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.56  fof(f134,plain,(
% 1.46/0.56    ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | spl3_11),
% 1.46/0.56    inference(avatar_component_clause,[],[f132])).
% 1.46/0.56  fof(f132,plain,(
% 1.46/0.56    spl3_11 <=> r1_tarski(k1_relat_1(sK1),k1_xboole_0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.46/0.56  fof(f298,plain,(
% 1.46/0.56    spl3_2 | ~spl3_3 | ~spl3_5 | spl3_9 | ~spl3_16),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f297])).
% 1.46/0.56  fof(f297,plain,(
% 1.46/0.56    $false | (spl3_2 | ~spl3_3 | ~spl3_5 | spl3_9 | ~spl3_16)),
% 1.46/0.56    inference(subsumption_resolution,[],[f283,f241])).
% 1.46/0.56  fof(f241,plain,(
% 1.46/0.56    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_3 | spl3_9 | ~spl3_16)),
% 1.46/0.56    inference(backward_demodulation,[],[f187,f221])).
% 1.46/0.56  fof(f187,plain,(
% 1.46/0.56    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | (spl3_2 | ~spl3_3 | spl3_9)),
% 1.46/0.56    inference(backward_demodulation,[],[f125,f177])).
% 1.46/0.56  fof(f125,plain,(
% 1.46/0.56    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1) | spl3_9),
% 1.46/0.56    inference(avatar_component_clause,[],[f124])).
% 1.46/0.56  fof(f124,plain,(
% 1.46/0.56    spl3_9 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.46/0.56  fof(f283,plain,(
% 1.46/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_16)),
% 1.46/0.56    inference(backward_demodulation,[],[f243,f279])).
% 1.46/0.56  fof(f243,plain,(
% 1.46/0.56    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl3_2 | ~spl3_3 | ~spl3_16)),
% 1.46/0.56    inference(backward_demodulation,[],[f189,f221])).
% 1.46/0.56  fof(f189,plain,(
% 1.46/0.56    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) | (spl3_2 | ~spl3_3)),
% 1.46/0.56    inference(backward_demodulation,[],[f169,f177])).
% 1.46/0.56  fof(f234,plain,(
% 1.46/0.56    spl3_15),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f233])).
% 1.46/0.56  fof(f233,plain,(
% 1.46/0.56    $false | spl3_15),
% 1.46/0.56    inference(subsumption_resolution,[],[f232,f38])).
% 1.46/0.56  fof(f232,plain,(
% 1.46/0.56    ~v1_xboole_0(k1_xboole_0) | spl3_15),
% 1.46/0.56    inference(resolution,[],[f224,f39])).
% 1.46/0.56  fof(f224,plain,(
% 1.46/0.56    r2_hidden(sK2(k1_xboole_0,sK1),k1_xboole_0) | spl3_15),
% 1.46/0.56    inference(resolution,[],[f217,f44])).
% 1.46/0.56  fof(f217,plain,(
% 1.46/0.56    ~r1_tarski(k1_xboole_0,sK1) | spl3_15),
% 1.46/0.56    inference(avatar_component_clause,[],[f215])).
% 1.46/0.56  fof(f215,plain,(
% 1.46/0.56    spl3_15 <=> r1_tarski(k1_xboole_0,sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.46/0.56  fof(f222,plain,(
% 1.46/0.56    ~spl3_15 | spl3_16 | spl3_2 | ~spl3_3),
% 1.46/0.56    inference(avatar_split_clause,[],[f213,f77,f73,f219,f215])).
% 1.46/0.56  fof(f213,plain,(
% 1.46/0.56    k1_xboole_0 = sK1 | ~r1_tarski(k1_xboole_0,sK1) | (spl3_2 | ~spl3_3)),
% 1.46/0.56    inference(resolution,[],[f204,f42])).
% 1.46/0.56  fof(f42,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f25])).
% 1.46/0.56  fof(f204,plain,(
% 1.46/0.56    r1_tarski(sK1,k1_xboole_0) | (spl3_2 | ~spl3_3)),
% 1.46/0.56    inference(forward_demodulation,[],[f190,f61])).
% 1.46/0.56  fof(f61,plain,(
% 1.46/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.46/0.56    inference(equality_resolution,[],[f50])).
% 1.46/0.56  fof(f50,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.46/0.56    inference(cnf_transformation,[],[f32])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.46/0.56    inference(flattening,[],[f31])).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.46/0.56    inference(nnf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.46/0.56  fof(f190,plain,(
% 1.46/0.56    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) | (spl3_2 | ~spl3_3)),
% 1.46/0.56    inference(backward_demodulation,[],[f170,f177])).
% 1.46/0.56  fof(f170,plain,(
% 1.46/0.56    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) | ~spl3_3),
% 1.46/0.56    inference(resolution,[],[f78,f46])).
% 1.46/0.56  fof(f46,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f30])).
% 1.46/0.56  fof(f30,plain,(
% 1.46/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.46/0.56    inference(nnf_transformation,[],[f6])).
% 1.46/0.56  fof(f6,axiom,(
% 1.46/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.46/0.56  fof(f175,plain,(
% 1.46/0.56    ~spl3_4 | spl3_5),
% 1.46/0.56    inference(avatar_split_clause,[],[f164,f92,f88])).
% 1.46/0.56  fof(f88,plain,(
% 1.46/0.56    spl3_4 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.46/0.56  fof(f164,plain,(
% 1.46/0.56    sK0 = k2_relat_1(sK1) | ~r1_tarski(sK0,k2_relat_1(sK1))),
% 1.46/0.56    inference(resolution,[],[f36,f42])).
% 1.46/0.56  fof(f36,plain,(
% 1.46/0.56    r1_tarski(k2_relat_1(sK1),sK0)),
% 1.46/0.56    inference(cnf_transformation,[],[f23])).
% 1.46/0.56  fof(f174,plain,(
% 1.46/0.56    spl3_2 | ~spl3_3 | spl3_6),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f173])).
% 1.46/0.56  fof(f173,plain,(
% 1.46/0.56    $false | (spl3_2 | ~spl3_3 | spl3_6)),
% 1.46/0.56    inference(subsumption_resolution,[],[f169,f172])).
% 1.46/0.56  fof(f172,plain,(
% 1.46/0.56    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | (spl3_2 | ~spl3_3 | spl3_6)),
% 1.46/0.56    inference(subsumption_resolution,[],[f171,f75])).
% 1.46/0.56  fof(f171,plain,(
% 1.46/0.56    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | (~spl3_3 | spl3_6)),
% 1.46/0.56    inference(subsumption_resolution,[],[f168,f113])).
% 1.46/0.56  fof(f113,plain,(
% 1.46/0.56    k1_xboole_0 != sK0 | spl3_6),
% 1.46/0.56    inference(avatar_component_clause,[],[f112])).
% 1.46/0.56  fof(f112,plain,(
% 1.46/0.56    spl3_6 <=> k1_xboole_0 = sK0),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.46/0.56  fof(f157,plain,(
% 1.46/0.56    spl3_4 | ~spl3_6),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f156])).
% 1.46/0.56  fof(f156,plain,(
% 1.46/0.56    $false | (spl3_4 | ~spl3_6)),
% 1.46/0.56    inference(subsumption_resolution,[],[f149,f38])).
% 1.46/0.56  fof(f149,plain,(
% 1.46/0.56    ~v1_xboole_0(k1_xboole_0) | (spl3_4 | ~spl3_6)),
% 1.46/0.56    inference(backward_demodulation,[],[f97,f114])).
% 1.46/0.56  fof(f114,plain,(
% 1.46/0.56    k1_xboole_0 = sK0 | ~spl3_6),
% 1.46/0.56    inference(avatar_component_clause,[],[f112])).
% 1.46/0.56  fof(f97,plain,(
% 1.46/0.56    ~v1_xboole_0(sK0) | spl3_4),
% 1.46/0.56    inference(resolution,[],[f96,f39])).
% 1.46/0.56  fof(f96,plain,(
% 1.46/0.56    r2_hidden(sK2(sK0,k2_relat_1(sK1)),sK0) | spl3_4),
% 1.46/0.56    inference(resolution,[],[f90,f44])).
% 1.46/0.56  fof(f90,plain,(
% 1.46/0.56    ~r1_tarski(sK0,k2_relat_1(sK1)) | spl3_4),
% 1.46/0.56    inference(avatar_component_clause,[],[f88])).
% 1.46/0.56  fof(f136,plain,(
% 1.46/0.56    spl3_10 | ~spl3_9 | ~spl3_11),
% 1.46/0.56    inference(avatar_split_clause,[],[f106,f132,f124,f128])).
% 1.46/0.56  fof(f106,plain,(
% 1.46/0.56    ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1) | v1_funct_2(sK1,k1_xboole_0,sK0)),
% 1.46/0.56    inference(resolution,[],[f86,f66])).
% 1.46/0.56  fof(f66,plain,(
% 1.46/0.56    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.46/0.56    inference(equality_resolution,[],[f56])).
% 1.46/0.56  fof(f56,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f33])).
% 1.46/0.56  fof(f86,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r1_tarski(k1_relat_1(sK1),X0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f83,f34])).
% 1.46/0.56  fof(f83,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r1_tarski(k1_relat_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 1.46/0.56    inference(resolution,[],[f36,f51])).
% 1.46/0.56  fof(f110,plain,(
% 1.46/0.56    spl3_3),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f109])).
% 1.46/0.56  fof(f109,plain,(
% 1.46/0.56    $false | spl3_3),
% 1.46/0.56    inference(subsumption_resolution,[],[f101,f60])).
% 1.46/0.56  fof(f101,plain,(
% 1.46/0.56    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | spl3_3),
% 1.46/0.56    inference(resolution,[],[f86,f79])).
% 1.46/0.56  fof(f79,plain,(
% 1.46/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl3_3),
% 1.46/0.56    inference(avatar_component_clause,[],[f77])).
% 1.46/0.56  fof(f82,plain,(
% 1.46/0.56    spl3_1),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f81])).
% 1.46/0.56  fof(f81,plain,(
% 1.46/0.56    $false | spl3_1),
% 1.46/0.56    inference(subsumption_resolution,[],[f71,f35])).
% 1.46/0.56  fof(f35,plain,(
% 1.46/0.56    v1_funct_1(sK1)),
% 1.46/0.56    inference(cnf_transformation,[],[f23])).
% 1.46/0.56  fof(f71,plain,(
% 1.46/0.56    ~v1_funct_1(sK1) | spl3_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f69])).
% 1.46/0.56  fof(f69,plain,(
% 1.46/0.56    spl3_1 <=> v1_funct_1(sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.46/0.56  fof(f80,plain,(
% 1.46/0.56    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.46/0.56    inference(avatar_split_clause,[],[f37,f77,f73,f69])).
% 1.46/0.56  fof(f37,plain,(
% 1.46/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 1.46/0.56    inference(cnf_transformation,[],[f23])).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (13078)------------------------------
% 1.46/0.56  % (13078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (13078)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (13078)Memory used [KB]: 10746
% 1.46/0.56  % (13078)Time elapsed: 0.129 s
% 1.46/0.56  % (13078)------------------------------
% 1.46/0.56  % (13078)------------------------------
% 1.46/0.56  % (13069)Success in time 0.188 s
%------------------------------------------------------------------------------
