%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 432 expanded)
%              Number of leaves         :   28 ( 119 expanded)
%              Depth                    :   18
%              Number of atoms          :  451 (1306 expanded)
%              Number of equality atoms :  131 ( 377 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f871,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f233,f408,f450,f461,f502,f519,f610,f806,f869])).

fof(f869,plain,
    ( spl5_2
    | ~ spl5_10
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f868])).

fof(f868,plain,
    ( $false
    | spl5_2
    | ~ spl5_10
    | spl5_12 ),
    inference(subsumption_resolution,[],[f867,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f867,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl5_2
    | ~ spl5_10
    | spl5_12 ),
    inference(forward_demodulation,[],[f864,f54])).

fof(f54,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f864,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK2)
    | spl5_2
    | ~ spl5_10
    | spl5_12 ),
    inference(backward_demodulation,[],[f106,f827])).

fof(f827,plain,
    ( k1_xboole_0 = sK3
    | spl5_2
    | ~ spl5_10
    | spl5_12 ),
    inference(forward_demodulation,[],[f826,f93])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f826,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,sK2)
    | spl5_2
    | ~ spl5_10
    | spl5_12 ),
    inference(forward_demodulation,[],[f367,f783])).

fof(f783,plain,
    ( k1_xboole_0 = sK1
    | spl5_2
    | spl5_12 ),
    inference(subsumption_resolution,[],[f782,f403])).

fof(f403,plain,
    ( k1_xboole_0 != sK2
    | spl5_12 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl5_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f782,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f777,f106])).

fof(f777,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f215,f356])).

fof(f356,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f352,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f352,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f87,f85])).

fof(f85,plain,(
    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).

fof(f50,plain,(
    r2_hidden(sK3,k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK3),sK2)
      | sK1 != k1_relat_1(sK3) )
    & r2_hidden(sK3,k1_funct_2(sK1,sK2))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK3),sK2)
        | sK1 != k1_relat_1(sK3) )
      & r2_hidden(sK3,k1_funct_2(sK1,sK2))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f75,f61])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f215,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
      | r1_tarski(k2_relat_1(X4),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f214,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f76,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f214,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k2_relat_1(X4),X3)
      | ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f211,f138])).

fof(f138,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f112,f90])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f211,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k2_relat_1(X4),X3)
      | ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
      | ~ v1_relat_1(k2_zfmisc_1(X2,X3))
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f57,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f367,plain,
    ( sK3 = k2_zfmisc_1(sK1,sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl5_10
  <=> sK3 = k2_zfmisc_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f106,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_2
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f806,plain,
    ( spl5_2
    | spl5_9
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f805])).

fof(f805,plain,
    ( $false
    | spl5_2
    | spl5_9
    | spl5_12 ),
    inference(subsumption_resolution,[],[f804,f55])).

fof(f804,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl5_2
    | spl5_9
    | spl5_12 ),
    inference(forward_demodulation,[],[f792,f93])).

fof(f792,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),sK3)
    | spl5_2
    | spl5_9
    | spl5_12 ),
    inference(backward_demodulation,[],[f363,f783])).

fof(f363,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),sK3)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl5_9
  <=> r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f610,plain,
    ( ~ spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f609,f365,f361])).

fof(f609,plain,
    ( sK3 = k2_zfmisc_1(sK1,sK2)
    | ~ r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) ),
    inference(resolution,[],[f356,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f519,plain,
    ( spl5_1
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | spl5_1
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f517,f53])).

fof(f53,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f517,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl5_1
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f516,f478])).

fof(f478,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_5 ),
    inference(resolution,[],[f228,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f228,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl5_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f516,plain,
    ( k1_relat_1(k1_xboole_0) != sK1
    | spl5_1
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f102,f480])).

fof(f480,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_12 ),
    inference(resolution,[],[f452,f120])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f65,f55])).

fof(f452,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f447,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f447,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0))
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f356,f404])).

fof(f404,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f402])).

fof(f102,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_1
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f502,plain,
    ( spl5_2
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | spl5_2
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f500,f452])).

fof(f500,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl5_2
    | ~ spl5_12 ),
    inference(resolution,[],[f441,f173])).

fof(f173,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f172,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f113,f67])).

fof(f113,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_relat_1(X1) ) ),
    inference(superposition,[],[f76,f92])).

fof(f172,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f171,f116])).

fof(f116,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f115,f55])).

fof(f171,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f57,f54])).

fof(f441,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | spl5_2
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f106,f404])).

fof(f461,plain,
    ( spl5_11
    | spl5_12 ),
    inference(avatar_split_clause,[],[f460,f402,f398])).

fof(f398,plain,
    ( spl5_11
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f460,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f459,f262])).

fof(f262,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(resolution,[],[f88,f85])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f61])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f459,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f354,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f354,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f352,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f31,f32])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f450,plain,
    ( spl5_6
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | spl5_6
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f443,f52])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f443,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_6
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f232,f404])).

fof(f232,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl5_6
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f408,plain,
    ( spl5_1
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | spl5_1
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f406,f102])).

fof(f406,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f353,f400])).

fof(f400,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f398])).

fof(f353,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f352,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f233,plain,
    ( spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f223,f230,f226])).

fof(f223,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f86,f110])).

fof(f110,plain,(
    ~ v1_xboole_0(k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
    inference(resolution,[],[f85,f59])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f62,f61])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f107,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f51,f104,f100])).

fof(f51,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | sK1 != k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:06:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (24844)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (24839)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (24860)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (24841)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (24855)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (24843)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (24842)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (24862)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (24852)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (24840)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (24853)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (24848)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (24840)Refutation not found, incomplete strategy% (24840)------------------------------
% 0.20/0.52  % (24840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24840)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24840)Memory used [KB]: 1663
% 0.20/0.52  % (24840)Time elapsed: 0.114 s
% 0.20/0.52  % (24840)------------------------------
% 0.20/0.52  % (24840)------------------------------
% 0.20/0.52  % (24853)Refutation not found, incomplete strategy% (24853)------------------------------
% 0.20/0.52  % (24853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24853)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24853)Memory used [KB]: 1791
% 0.20/0.52  % (24853)Time elapsed: 0.114 s
% 0.20/0.52  % (24853)------------------------------
% 0.20/0.52  % (24853)------------------------------
% 0.20/0.52  % (24854)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (24864)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (24855)Refutation not found, incomplete strategy% (24855)------------------------------
% 0.20/0.53  % (24855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24855)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24855)Memory used [KB]: 10618
% 0.20/0.53  % (24855)Time elapsed: 0.115 s
% 0.20/0.53  % (24855)------------------------------
% 0.20/0.53  % (24855)------------------------------
% 0.20/0.53  % (24857)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (24845)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (24868)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (24856)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (24849)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (24868)Refutation not found, incomplete strategy% (24868)------------------------------
% 0.20/0.53  % (24868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24868)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24868)Memory used [KB]: 1791
% 0.20/0.53  % (24868)Time elapsed: 0.131 s
% 0.20/0.53  % (24868)------------------------------
% 0.20/0.53  % (24868)------------------------------
% 0.20/0.54  % (24858)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (24867)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (24865)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (24846)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (24863)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (24851)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (24865)Refutation not found, incomplete strategy% (24865)------------------------------
% 0.20/0.54  % (24865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24863)Refutation not found, incomplete strategy% (24863)------------------------------
% 0.20/0.54  % (24863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24863)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (24863)Memory used [KB]: 10746
% 0.20/0.54  % (24863)Time elapsed: 0.129 s
% 0.20/0.54  % (24863)------------------------------
% 0.20/0.54  % (24863)------------------------------
% 0.20/0.54  % (24847)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (24865)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (24865)Memory used [KB]: 6268
% 0.20/0.54  % (24865)Time elapsed: 0.128 s
% 0.20/0.54  % (24865)------------------------------
% 0.20/0.54  % (24865)------------------------------
% 0.20/0.54  % (24856)Refutation not found, incomplete strategy% (24856)------------------------------
% 0.20/0.54  % (24856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24856)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (24856)Memory used [KB]: 1791
% 0.20/0.54  % (24856)Time elapsed: 0.130 s
% 0.20/0.54  % (24856)------------------------------
% 0.20/0.54  % (24856)------------------------------
% 0.20/0.55  % (24866)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (24866)Refutation not found, incomplete strategy% (24866)------------------------------
% 0.20/0.55  % (24866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (24866)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (24866)Memory used [KB]: 6268
% 0.20/0.55  % (24866)Time elapsed: 0.138 s
% 0.20/0.55  % (24866)------------------------------
% 0.20/0.55  % (24866)------------------------------
% 0.20/0.55  % (24850)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (24857)Refutation not found, incomplete strategy% (24857)------------------------------
% 0.20/0.55  % (24857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (24857)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (24857)Memory used [KB]: 1663
% 0.20/0.55  % (24857)Time elapsed: 0.139 s
% 0.20/0.55  % (24857)------------------------------
% 0.20/0.55  % (24857)------------------------------
% 0.20/0.55  % (24861)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (24850)Refutation not found, incomplete strategy% (24850)------------------------------
% 0.20/0.55  % (24850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (24859)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.56  % (24850)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (24850)Memory used [KB]: 6268
% 0.20/0.56  % (24850)Time elapsed: 0.142 s
% 0.20/0.56  % (24850)------------------------------
% 0.20/0.56  % (24850)------------------------------
% 0.20/0.56  % (24845)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f871,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f107,f233,f408,f450,f461,f502,f519,f610,f806,f869])).
% 0.20/0.56  fof(f869,plain,(
% 0.20/0.56    spl5_2 | ~spl5_10 | spl5_12),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f868])).
% 0.20/0.56  fof(f868,plain,(
% 0.20/0.56    $false | (spl5_2 | ~spl5_10 | spl5_12)),
% 0.20/0.56    inference(subsumption_resolution,[],[f867,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.56  fof(f867,plain,(
% 0.20/0.56    ~r1_tarski(k1_xboole_0,sK2) | (spl5_2 | ~spl5_10 | spl5_12)),
% 0.20/0.56    inference(forward_demodulation,[],[f864,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.56  fof(f864,plain,(
% 0.20/0.56    ~r1_tarski(k2_relat_1(k1_xboole_0),sK2) | (spl5_2 | ~spl5_10 | spl5_12)),
% 0.20/0.56    inference(backward_demodulation,[],[f106,f827])).
% 0.20/0.56  fof(f827,plain,(
% 0.20/0.56    k1_xboole_0 = sK3 | (spl5_2 | ~spl5_10 | spl5_12)),
% 0.20/0.56    inference(forward_demodulation,[],[f826,f93])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f69])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.56    inference(flattening,[],[f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.56  fof(f826,plain,(
% 0.20/0.56    sK3 = k2_zfmisc_1(k1_xboole_0,sK2) | (spl5_2 | ~spl5_10 | spl5_12)),
% 0.20/0.56    inference(forward_demodulation,[],[f367,f783])).
% 0.20/0.56  fof(f783,plain,(
% 0.20/0.56    k1_xboole_0 = sK1 | (spl5_2 | spl5_12)),
% 0.20/0.56    inference(subsumption_resolution,[],[f782,f403])).
% 0.20/0.56  fof(f403,plain,(
% 0.20/0.56    k1_xboole_0 != sK2 | spl5_12),
% 0.20/0.56    inference(avatar_component_clause,[],[f402])).
% 0.20/0.56  fof(f402,plain,(
% 0.20/0.56    spl5_12 <=> k1_xboole_0 = sK2),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.56  fof(f782,plain,(
% 0.20/0.56    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | spl5_2),
% 0.20/0.56    inference(subsumption_resolution,[],[f777,f106])).
% 0.20/0.56  fof(f777,plain,(
% 0.20/0.56    r1_tarski(k2_relat_1(sK3),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(resolution,[],[f215,f356])).
% 0.20/0.56  fof(f356,plain,(
% 0.20/0.56    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.56    inference(resolution,[],[f352,f66])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.56    inference(nnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.56  fof(f352,plain,(
% 0.20/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.56    inference(resolution,[],[f87,f85])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)))),
% 0.20/0.56    inference(definition_unfolding,[],[f50,f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,axiom,(
% 0.20/0.56    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    r2_hidden(sK3,k1_funct_2(sK1,sK2))),
% 0.20/0.56    inference(cnf_transformation,[],[f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    (~r1_tarski(k2_relat_1(sK3),sK2) | sK1 != k1_relat_1(sK3)) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK3),sK2) | sK1 != k1_relat_1(sK3)) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.56    inference(flattening,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.56    inference(ennf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.20/0.56    inference(negated_conjecture,[],[f17])).
% 0.20/0.56  fof(f17,conjecture,(
% 0.20/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f75,f61])).
% 0.20/0.56  fof(f75,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.20/0.56  fof(f215,plain,(
% 0.20/0.56    ( ! [X4,X2,X3] : (~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | r1_tarski(k2_relat_1(X4),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f214,f112])).
% 0.20/0.56  fof(f112,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0)) )),
% 0.20/0.56    inference(resolution,[],[f76,f67])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f42])).
% 0.20/0.56  fof(f76,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.56  fof(f214,plain,(
% 0.20/0.56    ( ! [X4,X2,X3] : (r1_tarski(k2_relat_1(X4),X3) | ~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | ~v1_relat_1(X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f211,f138])).
% 0.20/0.56  fof(f138,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.56    inference(resolution,[],[f112,f90])).
% 0.20/0.56  fof(f90,plain,(
% 0.20/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f64])).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f41])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(flattening,[],[f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.58  fof(f211,plain,(
% 0.20/0.58    ( ! [X4,X2,X3] : (r1_tarski(k2_relat_1(X4),X3) | ~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | ~v1_relat_1(k2_zfmisc_1(X2,X3)) | ~v1_relat_1(X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2) )),
% 0.20/0.58    inference(superposition,[],[f57,f72])).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.58    inference(ennf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(flattening,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.58  fof(f367,plain,(
% 0.20/0.58    sK3 = k2_zfmisc_1(sK1,sK2) | ~spl5_10),
% 0.20/0.58    inference(avatar_component_clause,[],[f365])).
% 0.20/0.58  fof(f365,plain,(
% 0.20/0.58    spl5_10 <=> sK3 = k2_zfmisc_1(sK1,sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.58  fof(f106,plain,(
% 0.20/0.58    ~r1_tarski(k2_relat_1(sK3),sK2) | spl5_2),
% 0.20/0.58    inference(avatar_component_clause,[],[f104])).
% 0.20/0.58  fof(f104,plain,(
% 0.20/0.58    spl5_2 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.58  fof(f806,plain,(
% 0.20/0.58    spl5_2 | spl5_9 | spl5_12),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f805])).
% 0.20/0.58  fof(f805,plain,(
% 0.20/0.58    $false | (spl5_2 | spl5_9 | spl5_12)),
% 0.20/0.58    inference(subsumption_resolution,[],[f804,f55])).
% 0.20/0.58  fof(f804,plain,(
% 0.20/0.58    ~r1_tarski(k1_xboole_0,sK3) | (spl5_2 | spl5_9 | spl5_12)),
% 0.20/0.58    inference(forward_demodulation,[],[f792,f93])).
% 0.20/0.58  fof(f792,plain,(
% 0.20/0.58    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK2),sK3) | (spl5_2 | spl5_9 | spl5_12)),
% 0.20/0.58    inference(backward_demodulation,[],[f363,f783])).
% 0.20/0.58  fof(f363,plain,(
% 0.20/0.58    ~r1_tarski(k2_zfmisc_1(sK1,sK2),sK3) | spl5_9),
% 0.20/0.58    inference(avatar_component_clause,[],[f361])).
% 0.20/0.58  fof(f361,plain,(
% 0.20/0.58    spl5_9 <=> r1_tarski(k2_zfmisc_1(sK1,sK2),sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.58  fof(f610,plain,(
% 0.20/0.58    ~spl5_9 | spl5_10),
% 0.20/0.58    inference(avatar_split_clause,[],[f609,f365,f361])).
% 0.20/0.58  fof(f609,plain,(
% 0.20/0.58    sK3 = k2_zfmisc_1(sK1,sK2) | ~r1_tarski(k2_zfmisc_1(sK1,sK2),sK3)),
% 0.20/0.58    inference(resolution,[],[f356,f65])).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f41])).
% 0.20/0.58  fof(f519,plain,(
% 0.20/0.58    spl5_1 | ~spl5_5 | ~spl5_12),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f518])).
% 0.20/0.58  fof(f518,plain,(
% 0.20/0.58    $false | (spl5_1 | ~spl5_5 | ~spl5_12)),
% 0.20/0.58    inference(subsumption_resolution,[],[f517,f53])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f517,plain,(
% 0.20/0.58    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (spl5_1 | ~spl5_5 | ~spl5_12)),
% 0.20/0.58    inference(forward_demodulation,[],[f516,f478])).
% 0.20/0.58  fof(f478,plain,(
% 0.20/0.58    k1_xboole_0 = sK1 | ~spl5_5),
% 0.20/0.58    inference(resolution,[],[f228,f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.58  fof(f228,plain,(
% 0.20/0.58    v1_xboole_0(sK1) | ~spl5_5),
% 0.20/0.58    inference(avatar_component_clause,[],[f226])).
% 0.20/0.58  fof(f226,plain,(
% 0.20/0.58    spl5_5 <=> v1_xboole_0(sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.58  fof(f516,plain,(
% 0.20/0.58    k1_relat_1(k1_xboole_0) != sK1 | (spl5_1 | ~spl5_12)),
% 0.20/0.58    inference(forward_demodulation,[],[f102,f480])).
% 0.20/0.58  fof(f480,plain,(
% 0.20/0.58    k1_xboole_0 = sK3 | ~spl5_12),
% 0.20/0.58    inference(resolution,[],[f452,f120])).
% 0.20/0.58  fof(f120,plain,(
% 0.20/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.58    inference(resolution,[],[f65,f55])).
% 0.20/0.58  fof(f452,plain,(
% 0.20/0.58    r1_tarski(sK3,k1_xboole_0) | ~spl5_12),
% 0.20/0.58    inference(forward_demodulation,[],[f447,f92])).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f70])).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f44])).
% 0.20/0.58  fof(f447,plain,(
% 0.20/0.58    r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) | ~spl5_12),
% 0.20/0.58    inference(backward_demodulation,[],[f356,f404])).
% 0.20/0.58  fof(f404,plain,(
% 0.20/0.58    k1_xboole_0 = sK2 | ~spl5_12),
% 0.20/0.58    inference(avatar_component_clause,[],[f402])).
% 0.20/0.58  fof(f102,plain,(
% 0.20/0.58    sK1 != k1_relat_1(sK3) | spl5_1),
% 0.20/0.58    inference(avatar_component_clause,[],[f100])).
% 0.20/0.58  fof(f100,plain,(
% 0.20/0.58    spl5_1 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.58  fof(f502,plain,(
% 0.20/0.58    spl5_2 | ~spl5_12),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f501])).
% 0.20/0.58  fof(f501,plain,(
% 0.20/0.58    $false | (spl5_2 | ~spl5_12)),
% 0.20/0.58    inference(subsumption_resolution,[],[f500,f452])).
% 0.20/0.58  fof(f500,plain,(
% 0.20/0.58    ~r1_tarski(sK3,k1_xboole_0) | (spl5_2 | ~spl5_12)),
% 0.20/0.58    inference(resolution,[],[f441,f173])).
% 0.20/0.58  fof(f173,plain,(
% 0.20/0.58    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f172,f115])).
% 0.20/0.58  fof(f115,plain,(
% 0.20/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_relat_1(X0)) )),
% 0.20/0.58    inference(resolution,[],[f113,f67])).
% 0.20/0.58  fof(f113,plain,(
% 0.20/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_relat_1(X1)) )),
% 0.20/0.58    inference(superposition,[],[f76,f92])).
% 0.20/0.58  fof(f172,plain,(
% 0.20/0.58    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f171,f116])).
% 0.20/0.58  fof(f116,plain,(
% 0.20/0.58    v1_relat_1(k1_xboole_0)),
% 0.20/0.58    inference(resolution,[],[f115,f55])).
% 0.20/0.58  fof(f171,plain,(
% 0.20/0.58    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(superposition,[],[f57,f54])).
% 0.20/0.58  fof(f441,plain,(
% 0.20/0.58    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | (spl5_2 | ~spl5_12)),
% 0.20/0.58    inference(backward_demodulation,[],[f106,f404])).
% 0.20/0.58  fof(f461,plain,(
% 0.20/0.58    spl5_11 | spl5_12),
% 0.20/0.58    inference(avatar_split_clause,[],[f460,f402,f398])).
% 0.20/0.58  fof(f398,plain,(
% 0.20/0.58    spl5_11 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.58  fof(f460,plain,(
% 0.20/0.58    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.58    inference(subsumption_resolution,[],[f459,f262])).
% 0.20/0.58  fof(f262,plain,(
% 0.20/0.58    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.58    inference(resolution,[],[f88,f85])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f74,f61])).
% 0.20/0.58  fof(f74,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f27])).
% 0.20/0.58  fof(f459,plain,(
% 0.20/0.58    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.58    inference(resolution,[],[f354,f78])).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.20/0.58    inference(rectify,[],[f45])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f32])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.58  fof(f354,plain,(
% 0.20/0.58    sP0(sK1,sK3,sK2)),
% 0.20/0.58    inference(resolution,[],[f352,f82])).
% 0.20/0.58  fof(f82,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f47])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(nnf_transformation,[],[f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(definition_folding,[],[f31,f32])).
% 0.20/0.58  fof(f31,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(flattening,[],[f30])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(ennf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.58  fof(f450,plain,(
% 0.20/0.58    spl5_6 | ~spl5_12),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f449])).
% 0.20/0.58  fof(f449,plain,(
% 0.20/0.58    $false | (spl5_6 | ~spl5_12)),
% 0.20/0.58    inference(subsumption_resolution,[],[f443,f52])).
% 0.20/0.58  fof(f52,plain,(
% 0.20/0.58    v1_xboole_0(k1_xboole_0)),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    v1_xboole_0(k1_xboole_0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.58  fof(f443,plain,(
% 0.20/0.58    ~v1_xboole_0(k1_xboole_0) | (spl5_6 | ~spl5_12)),
% 0.20/0.58    inference(backward_demodulation,[],[f232,f404])).
% 0.20/0.58  fof(f232,plain,(
% 0.20/0.58    ~v1_xboole_0(sK2) | spl5_6),
% 0.20/0.58    inference(avatar_component_clause,[],[f230])).
% 0.20/0.58  fof(f230,plain,(
% 0.20/0.58    spl5_6 <=> v1_xboole_0(sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.58  fof(f408,plain,(
% 0.20/0.58    spl5_1 | ~spl5_11),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f407])).
% 0.20/0.58  fof(f407,plain,(
% 0.20/0.58    $false | (spl5_1 | ~spl5_11)),
% 0.20/0.58    inference(subsumption_resolution,[],[f406,f102])).
% 0.20/0.58  fof(f406,plain,(
% 0.20/0.58    sK1 = k1_relat_1(sK3) | ~spl5_11),
% 0.20/0.58    inference(backward_demodulation,[],[f353,f400])).
% 0.20/0.58  fof(f400,plain,(
% 0.20/0.58    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl5_11),
% 0.20/0.58    inference(avatar_component_clause,[],[f398])).
% 0.20/0.58  fof(f353,plain,(
% 0.20/0.58    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.58    inference(resolution,[],[f352,f77])).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(ennf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.58  fof(f233,plain,(
% 0.20/0.58    spl5_5 | ~spl5_6),
% 0.20/0.58    inference(avatar_split_clause,[],[f223,f230,f226])).
% 0.20/0.58  fof(f223,plain,(
% 0.20/0.58    ~v1_xboole_0(sK2) | v1_xboole_0(sK1)),
% 0.20/0.58    inference(resolution,[],[f86,f110])).
% 0.20/0.58  fof(f110,plain,(
% 0.20/0.58    ~v1_xboole_0(k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)))),
% 0.20/0.58    inference(resolution,[],[f85,f59])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(rectify,[],[f36])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(nnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.58  fof(f86,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f62,f61])).
% 0.20/0.58  fof(f62,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f25])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f24])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,axiom,(
% 0.20/0.58    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).
% 0.20/0.58  fof(f107,plain,(
% 0.20/0.58    ~spl5_1 | ~spl5_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f51,f104,f100])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ~r1_tarski(k2_relat_1(sK3),sK2) | sK1 != k1_relat_1(sK3)),
% 0.20/0.58    inference(cnf_transformation,[],[f35])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (24845)------------------------------
% 0.20/0.58  % (24845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (24845)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (24845)Memory used [KB]: 11001
% 0.20/0.58  % (24845)Time elapsed: 0.139 s
% 0.20/0.58  % (24845)------------------------------
% 0.20/0.58  % (24845)------------------------------
% 0.20/0.59  % (24838)Success in time 0.219 s
%------------------------------------------------------------------------------
