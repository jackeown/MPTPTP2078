%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 494 expanded)
%              Number of leaves         :   30 ( 145 expanded)
%              Depth                    :   17
%              Number of atoms          :  676 (2187 expanded)
%              Number of equality atoms :  113 ( 397 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8325)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (8328)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f633,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f151,f162,f168,f174,f190,f192,f201,f206,f329,f387,f415,f450,f555,f632])).

fof(f632,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | spl3_9
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f631])).

fof(f631,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | spl3_9
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f630,f80])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f630,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | spl3_9
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f629,f601])).

fof(f601,plain,
    ( k1_xboole_0 != sK0
    | spl3_9
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f591,f600])).

fof(f600,plain,
    ( k1_xboole_0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f599,f77])).

fof(f77,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f599,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f598,f189])).

fof(f189,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f598,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(sK0,sK1,k1_xboole_0)
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f178,f445])).

fof(f445,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_12 ),
    inference(resolution,[],[f200,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (8335)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f200,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl3_12
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f178,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f72,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f64])).

fof(f64,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f591,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | spl3_9
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f590,f189])).

fof(f590,plain,
    ( sK0 != k1_relset_1(sK0,sK1,k1_xboole_0)
    | spl3_9
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f184,f445])).

fof(f184,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl3_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f629,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f624,f560])).

fof(f560,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f559,f525])).

fof(f525,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(resolution,[],[f479,f89])).

fof(f479,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f250,f445])).

fof(f250,plain,
    ( v1_xboole_0(k4_relat_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl3_18
  <=> v1_xboole_0(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f559,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f558,f445])).

fof(f558,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f231,f189])).

fof(f231,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | spl3_2
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f135,f173])).

fof(f173,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl3_8
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f135,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f624,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(trivial_inequality_removal,[],[f623])).

fof(f623,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(superposition,[],[f117,f621])).

fof(f621,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f620,f77])).

fof(f620,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f570,f582])).

fof(f582,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f474,f525])).

fof(f474,plain,
    ( k2_funct_1(k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f173,f445])).

fof(f570,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(resolution,[],[f557,f113])).

fof(f557,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f556,f445])).

fof(f556,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f138,f189])).

fof(f138,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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

fof(f555,plain,
    ( spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f546,f80])).

fof(f546,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f541,f525])).

fof(f541,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f412,f445])).

fof(f412,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f330,f189])).

fof(f330,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f139,f173])).

fof(f139,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f137])).

fof(f450,plain,
    ( ~ spl3_12
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | ~ spl3_12
    | spl3_18 ),
    inference(subsumption_resolution,[],[f448,f200])).

fof(f448,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_18 ),
    inference(resolution,[],[f251,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

fof(f251,plain,
    ( ~ v1_xboole_0(k4_relat_1(sK2))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f249])).

fof(f415,plain,
    ( ~ spl3_10
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | ~ spl3_10
    | spl3_11 ),
    inference(subsumption_resolution,[],[f408,f76])).

fof(f76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f408,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_10
    | spl3_11 ),
    inference(backward_demodulation,[],[f196,f189])).

fof(f196,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl3_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f387,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f379,f122])).

fof(f122,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f379,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl3_1
    | spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(resolution,[],[f378,f330])).

fof(f378,plain,
    ( ! [X1] :
        ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(sK0,X1) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f301,f302])).

fof(f302,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f178,f185])).

fof(f185,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f183])).

fof(f301,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X1)
        | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f300,f265])).

fof(f265,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f167,f173])).

fof(f167,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl3_7
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f300,plain,
    ( ! [X1] :
        ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f299,f230])).

fof(f230,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f150,f173])).

fof(f150,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f299,plain,
    ( ! [X1] :
        ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1)
        | ~ v1_relat_1(k4_relat_1(sK2)) )
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f294,f232])).

fof(f232,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f130,f173])).

fof(f130,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f294,plain,
    ( ! [X1] :
        ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1)
        | ~ v1_funct_1(k4_relat_1(sK2))
        | ~ v1_relat_1(k4_relat_1(sK2)) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f108,f288])).

fof(f288,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f264,f287])).

fof(f287,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f177,f74])).

fof(f74,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f177,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f72,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f264,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f161,f173])).

fof(f161,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_6
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f329,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f327,f122])).

fof(f327,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(resolution,[],[f326,f231])).

fof(f326,plain,
    ( ! [X0] :
        ( v1_funct_2(k4_relat_1(sK2),sK1,X0)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f298,f302])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | v1_funct_2(k4_relat_1(sK2),sK1,X0) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f297,f265])).

fof(f297,plain,
    ( ! [X0] :
        ( v1_funct_2(k4_relat_1(sK2),sK1,X0)
        | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f296,f230])).

fof(f296,plain,
    ( ! [X0] :
        ( v1_funct_2(k4_relat_1(sK2),sK1,X0)
        | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0)
        | ~ v1_relat_1(k4_relat_1(sK2)) )
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f293,f232])).

fof(f293,plain,
    ( ! [X0] :
        ( v1_funct_2(k4_relat_1(sK2),sK1,X0)
        | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0)
        | ~ v1_funct_1(k4_relat_1(sK2))
        | ~ v1_relat_1(k4_relat_1(sK2)) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f107,f288])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f206,plain,
    ( spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f202,f145])).

fof(f145,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f202,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f175,f70])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f175,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f131,f99])).

fof(f99,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f131,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f201,plain,
    ( ~ spl3_11
    | spl3_12 ),
    inference(avatar_split_clause,[],[f180,f198,f194])).

fof(f180,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f72,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f192,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f179,f146])).

fof(f146,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f179,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f72,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f190,plain,
    ( spl3_9
    | spl3_10 ),
    inference(avatar_split_clause,[],[f181,f187,f183])).

fof(f181,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f176,f71])).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f176,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f72,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f174,plain,
    ( ~ spl3_4
    | spl3_8 ),
    inference(avatar_split_clause,[],[f169,f171,f144])).

fof(f169,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f156,f70])).

fof(f156,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f73,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f168,plain,
    ( ~ spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f163,f165,f144])).

fof(f163,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f155,f70])).

fof(f155,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f162,plain,
    ( ~ spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f157,f159,f144])).

fof(f157,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f154,f70])).

fof(f154,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f151,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f141,f148,f144])).

fof(f141,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f70,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f140,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f75,f137,f133,f129])).

fof(f75,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:12:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (8321)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (8345)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (8322)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (8331)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (8343)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (8329)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (8323)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (8321)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  % (8325)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (8328)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  fof(f633,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f140,f151,f162,f168,f174,f190,f192,f201,f206,f329,f387,f415,f450,f555,f632])).
% 0.21/0.54  fof(f632,plain,(
% 0.21/0.54    spl3_2 | ~spl3_3 | ~spl3_8 | spl3_9 | ~spl3_10 | ~spl3_12 | ~spl3_18),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f631])).
% 0.21/0.54  fof(f631,plain,(
% 0.21/0.54    $false | (spl3_2 | ~spl3_3 | ~spl3_8 | spl3_9 | ~spl3_10 | ~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f630,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.54  fof(f630,plain,(
% 0.21/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_2 | ~spl3_3 | ~spl3_8 | spl3_9 | ~spl3_10 | ~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f629,f601])).
% 0.21/0.54  fof(f601,plain,(
% 0.21/0.54    k1_xboole_0 != sK0 | (spl3_9 | ~spl3_10 | ~spl3_12)),
% 0.21/0.54    inference(backward_demodulation,[],[f591,f600])).
% 0.21/0.54  fof(f600,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (~spl3_10 | ~spl3_12)),
% 0.21/0.54    inference(forward_demodulation,[],[f599,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.54  fof(f599,plain,(
% 0.21/0.54    k1_relat_1(k1_xboole_0) = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (~spl3_10 | ~spl3_12)),
% 0.21/0.54    inference(forward_demodulation,[],[f598,f189])).
% 0.21/0.54  fof(f189,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl3_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f187])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    spl3_10 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.54  fof(f598,plain,(
% 0.21/0.54    k1_relat_1(k1_xboole_0) = k1_relset_1(sK0,sK1,k1_xboole_0) | ~spl3_12),
% 0.21/0.54    inference(forward_demodulation,[],[f178,f445])).
% 0.21/0.54  fof(f445,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~spl3_12),
% 0.21/0.54    inference(resolution,[],[f200,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  % (8335)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.54  fof(f200,plain,(
% 0.21/0.54    v1_xboole_0(sK2) | ~spl3_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f198])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    spl3_12 <=> v1_xboole_0(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    inference(resolution,[],[f72,f113])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f29])).
% 0.21/0.54  fof(f29,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.54  fof(f591,plain,(
% 0.21/0.54    sK0 != k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (spl3_9 | ~spl3_10 | ~spl3_12)),
% 0.21/0.54    inference(forward_demodulation,[],[f590,f189])).
% 0.21/0.54  fof(f590,plain,(
% 0.21/0.54    sK0 != k1_relset_1(sK0,sK1,k1_xboole_0) | (spl3_9 | ~spl3_12)),
% 0.21/0.54    inference(forward_demodulation,[],[f184,f445])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    sK0 != k1_relset_1(sK0,sK1,sK2) | spl3_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f183])).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    spl3_9 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.54  fof(f629,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_2 | ~spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f624,f560])).
% 0.21/0.54  fof(f560,plain,(
% 0.21/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl3_2 | ~spl3_8 | ~spl3_10 | ~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(forward_demodulation,[],[f559,f525])).
% 0.21/0.54  fof(f525,plain,(
% 0.21/0.54    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(resolution,[],[f479,f89])).
% 0.21/0.54  fof(f479,plain,(
% 0.21/0.54    v1_xboole_0(k4_relat_1(k1_xboole_0)) | (~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(backward_demodulation,[],[f250,f445])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    v1_xboole_0(k4_relat_1(sK2)) | ~spl3_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f249])).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    spl3_18 <=> v1_xboole_0(k4_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.54  fof(f559,plain,(
% 0.21/0.54    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | (spl3_2 | ~spl3_8 | ~spl3_10 | ~spl3_12)),
% 0.21/0.54    inference(forward_demodulation,[],[f558,f445])).
% 0.21/0.54  fof(f558,plain,(
% 0.21/0.54    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | (spl3_2 | ~spl3_8 | ~spl3_10)),
% 0.21/0.54    inference(forward_demodulation,[],[f231,f189])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | (spl3_2 | ~spl3_8)),
% 0.21/0.54    inference(backward_demodulation,[],[f135,f173])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl3_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f171])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    spl3_8 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f133])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f624,plain,(
% 0.21/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f623])).
% 0.21/0.54  fof(f623,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(superposition,[],[f117,f621])).
% 0.21/0.54  fof(f621,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(forward_demodulation,[],[f620,f77])).
% 0.21/0.54  fof(f620,plain,(
% 0.21/0.54    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | (~spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(forward_demodulation,[],[f570,f582])).
% 0.21/0.54  fof(f582,plain,(
% 0.21/0.54    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_8 | ~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(forward_demodulation,[],[f474,f525])).
% 0.21/0.54  fof(f474,plain,(
% 0.21/0.54    k2_funct_1(k1_xboole_0) = k4_relat_1(k1_xboole_0) | (~spl3_8 | ~spl3_12)),
% 0.21/0.54    inference(backward_demodulation,[],[f173,f445])).
% 0.21/0.54  fof(f570,plain,(
% 0.21/0.54    k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | (~spl3_3 | ~spl3_10 | ~spl3_12)),
% 0.21/0.54    inference(resolution,[],[f557,f113])).
% 0.21/0.54  fof(f557,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_3 | ~spl3_10 | ~spl3_12)),
% 0.21/0.54    inference(forward_demodulation,[],[f556,f445])).
% 0.21/0.54  fof(f556,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_3 | ~spl3_10)),
% 0.21/0.54    inference(forward_demodulation,[],[f138,f189])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f137])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  fof(f555,plain,(
% 0.21/0.54    spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_12 | ~spl3_18),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f554])).
% 0.21/0.54  fof(f554,plain,(
% 0.21/0.54    $false | (spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f546,f80])).
% 0.21/0.54  fof(f546,plain,(
% 0.21/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_12 | ~spl3_18)),
% 0.21/0.54    inference(backward_demodulation,[],[f541,f525])).
% 0.21/0.54  fof(f541,plain,(
% 0.21/0.54    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_12)),
% 0.21/0.54    inference(forward_demodulation,[],[f412,f445])).
% 0.21/0.54  fof(f412,plain,(
% 0.21/0.54    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_8 | ~spl3_10)),
% 0.21/0.54    inference(backward_demodulation,[],[f330,f189])).
% 0.21/0.54  fof(f330,plain,(
% 0.21/0.54    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl3_3 | ~spl3_8)),
% 0.21/0.54    inference(forward_demodulation,[],[f139,f173])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f137])).
% 0.21/0.54  fof(f450,plain,(
% 0.21/0.54    ~spl3_12 | spl3_18),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f449])).
% 0.21/0.54  fof(f449,plain,(
% 0.21/0.54    $false | (~spl3_12 | spl3_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f448,f200])).
% 0.21/0.54  fof(f448,plain,(
% 0.21/0.54    ~v1_xboole_0(sK2) | spl3_18),
% 0.21/0.54    inference(resolution,[],[f251,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).
% 0.21/0.54  fof(f251,plain,(
% 0.21/0.54    ~v1_xboole_0(k4_relat_1(sK2)) | spl3_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f249])).
% 0.21/0.54  fof(f415,plain,(
% 0.21/0.54    ~spl3_10 | spl3_11),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f414])).
% 0.21/0.54  fof(f414,plain,(
% 0.21/0.54    $false | (~spl3_10 | spl3_11)),
% 0.21/0.54    inference(subsumption_resolution,[],[f408,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f408,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | (~spl3_10 | spl3_11)),
% 0.21/0.54    inference(backward_demodulation,[],[f196,f189])).
% 0.21/0.54  fof(f196,plain,(
% 0.21/0.54    ~v1_xboole_0(sK1) | spl3_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f194])).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    spl3_11 <=> v1_xboole_0(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.54  fof(f387,plain,(
% 0.21/0.54    ~spl3_1 | spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f386])).
% 0.21/0.54  fof(f386,plain,(
% 0.21/0.54    $false | (~spl3_1 | spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.21/0.54    inference(subsumption_resolution,[],[f379,f122])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f109])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f379,plain,(
% 0.21/0.54    ~r1_tarski(sK0,sK0) | (~spl3_1 | spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.21/0.54    inference(resolution,[],[f378,f330])).
% 0.21/0.54  fof(f378,plain,(
% 0.21/0.54    ( ! [X1] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(sK0,X1)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.21/0.54    inference(forward_demodulation,[],[f301,f302])).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    sK0 = k1_relat_1(sK2) | ~spl3_9),
% 0.21/0.54    inference(forward_demodulation,[],[f178,f185])).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f183])).
% 0.21/0.54  fof(f301,plain,(
% 0.21/0.54    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.54    inference(forward_demodulation,[],[f300,f265])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | (~spl3_7 | ~spl3_8)),
% 0.21/0.54    inference(forward_demodulation,[],[f167,f173])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f165])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    spl3_7 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.54  fof(f300,plain,(
% 0.21/0.54    ( ! [X1] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f299,f230])).
% 0.21/0.54  fof(f230,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(sK2)) | (~spl3_5 | ~spl3_8)),
% 0.21/0.54    inference(backward_demodulation,[],[f150,f173])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f148])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    spl3_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.54  fof(f299,plain,(
% 0.21/0.54    ( ! [X1] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1) | ~v1_relat_1(k4_relat_1(sK2))) ) | (~spl3_1 | ~spl3_6 | ~spl3_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f294,f232])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    v1_funct_1(k4_relat_1(sK2)) | (~spl3_1 | ~spl3_8)),
% 0.21/0.54    inference(backward_demodulation,[],[f130,f173])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f129])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.54  fof(f294,plain,(
% 0.21/0.54    ( ! [X1] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X1) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))) ) | (~spl3_6 | ~spl3_8)),
% 0.21/0.54    inference(superposition,[],[f108,f288])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    sK1 = k1_relat_1(k4_relat_1(sK2)) | (~spl3_6 | ~spl3_8)),
% 0.21/0.54    inference(backward_demodulation,[],[f264,f287])).
% 0.21/0.54  fof(f287,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2)),
% 0.21/0.54    inference(forward_demodulation,[],[f177,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f65])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f72,f114])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | (~spl3_6 | ~spl3_8)),
% 0.21/0.54    inference(forward_demodulation,[],[f161,f173])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f159])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    spl3_6 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.54  fof(f329,plain,(
% 0.21/0.54    ~spl3_1 | spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f328])).
% 0.21/0.54  fof(f328,plain,(
% 0.21/0.54    $false | (~spl3_1 | spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.21/0.54    inference(subsumption_resolution,[],[f327,f122])).
% 0.21/0.54  fof(f327,plain,(
% 0.21/0.54    ~r1_tarski(sK0,sK0) | (~spl3_1 | spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.21/0.54    inference(resolution,[],[f326,f231])).
% 0.21/0.54  fof(f326,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),sK1,X0) | ~r1_tarski(sK0,X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.21/0.54    inference(forward_demodulation,[],[f298,f302])).
% 0.21/0.54  fof(f298,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k4_relat_1(sK2),sK1,X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.54    inference(forward_demodulation,[],[f297,f265])).
% 0.21/0.54  fof(f297,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),sK1,X0) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f296,f230])).
% 0.21/0.54  fof(f296,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),sK1,X0) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) | ~v1_relat_1(k4_relat_1(sK2))) ) | (~spl3_1 | ~spl3_6 | ~spl3_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f293,f232])).
% 0.21/0.54  fof(f293,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),sK1,X0) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))) ) | (~spl3_6 | ~spl3_8)),
% 0.21/0.54    inference(superposition,[],[f107,f288])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f58])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    spl3_1 | ~spl3_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f205])).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    $false | (spl3_1 | ~spl3_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f202,f145])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl3_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f144])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    spl3_4 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | spl3_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f175,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f65])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.21/0.54    inference(resolution,[],[f131,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f129])).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    ~spl3_11 | spl3_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f180,f198,f194])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    v1_xboole_0(sK2) | ~v1_xboole_0(sK1)),
% 0.21/0.54    inference(resolution,[],[f72,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.54  fof(f192,plain,(
% 0.21/0.54    spl3_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    $false | spl3_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f179,f146])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | spl3_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f144])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f72,f112])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f190,plain,(
% 0.21/0.54    spl3_9 | spl3_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f181,f187,f183])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f176,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f65])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    inference(resolution,[],[f72,f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f69])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ~spl3_4 | spl3_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f169,f171,f144])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f156,f70])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f73,f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    v2_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f65])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ~spl3_4 | spl3_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f163,f165,f144])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f155,f70])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f73,f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ~spl3_4 | spl3_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f157,f159,f144])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f154,f70])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f73,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f51])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ~spl3_4 | spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f141,f148,f144])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f70,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f75,f137,f133,f129])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f65])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (8321)------------------------------
% 0.21/0.55  % (8321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8321)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (8321)Memory used [KB]: 10874
% 0.21/0.55  % (8321)Time elapsed: 0.108 s
% 0.21/0.55  % (8321)------------------------------
% 0.21/0.55  % (8321)------------------------------
% 0.21/0.55  % (8339)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (8319)Success in time 0.187 s
%------------------------------------------------------------------------------
