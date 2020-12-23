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
% DateTime   : Thu Dec  3 13:01:28 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 482 expanded)
%              Number of leaves         :   28 ( 157 expanded)
%              Depth                    :   18
%              Number of atoms          :  548 (3445 expanded)
%              Number of equality atoms :  130 (1026 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f542,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f172,f222,f240,f398,f433,f437,f483,f487,f495,f541])).

fof(f541,plain,
    ( ~ spl8_5
    | ~ spl8_37
    | ~ spl8_41 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_37
    | ~ spl8_41 ),
    inference(subsumption_resolution,[],[f539,f128])).

fof(f128,plain,(
    sK4 != k2_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f117,f51])).

fof(f51,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( sK4 != k2_relset_1(sK3,sK4,sK6)
    & k1_xboole_0 != sK5
    & v2_funct_1(sK7)
    & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f17,f39,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK4 != k2_relset_1(sK3,sK4,sK6)
          & k1_xboole_0 != sK5
          & v2_funct_1(X4)
          & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
          & v1_funct_2(X4,sK4,sK5)
          & v1_funct_1(X4) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X4] :
        ( sK4 != k2_relset_1(sK3,sK4,sK6)
        & k1_xboole_0 != sK5
        & v2_funct_1(X4)
        & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
        & v1_funct_2(X4,sK4,sK5)
        & v1_funct_1(X4) )
   => ( sK4 != k2_relset_1(sK3,sK4,sK6)
      & k1_xboole_0 != sK5
      & v2_funct_1(sK7)
      & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

fof(f117,plain,
    ( sK4 != k2_relat_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(superposition,[],[f58,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f58,plain,(
    sK4 != k2_relset_1(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f539,plain,
    ( sK4 = k2_relat_1(sK6)
    | ~ spl8_5
    | ~ spl8_37
    | ~ spl8_41 ),
    inference(backward_demodulation,[],[f478,f525])).

fof(f525,plain,
    ( sK4 = k10_relat_1(sK7,sK5)
    | ~ spl8_5
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f524,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f524,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = k10_relat_1(sK7,sK5)
    | ~ spl8_5
    | ~ spl8_37 ),
    inference(forward_demodulation,[],[f523,f167])).

fof(f167,plain,
    ( sK4 = k1_relat_1(sK7)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl8_5
  <=> sK4 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f523,plain,
    ( sK4 = k10_relat_1(sK7,sK5)
    | ~ r1_tarski(sK4,k1_relat_1(sK7))
    | ~ spl8_5
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f522,f91])).

fof(f91,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f68,f54])).

fof(f54,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f522,plain,
    ( sK4 = k10_relat_1(sK7,sK5)
    | ~ r1_tarski(sK4,k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ spl8_5
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f521,f52])).

fof(f52,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f521,plain,
    ( sK4 = k10_relat_1(sK7,sK5)
    | ~ r1_tarski(sK4,k1_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_5
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f520,f56])).

fof(f56,plain,(
    v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f520,plain,
    ( sK4 = k10_relat_1(sK7,sK5)
    | ~ v2_funct_1(sK7)
    | ~ r1_tarski(sK4,k1_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_5
    | ~ spl8_37 ),
    inference(superposition,[],[f64,f512])).

fof(f512,plain,
    ( sK5 = k9_relat_1(sK7,sK4)
    | ~ spl8_5
    | ~ spl8_37 ),
    inference(forward_demodulation,[],[f511,f392])).

fof(f392,plain,
    ( sK5 = k2_relat_1(sK7)
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl8_37
  <=> sK5 = k2_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f511,plain,
    ( k2_relat_1(sK7) = k9_relat_1(sK7,sK4)
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f510,f91])).

fof(f510,plain,
    ( k2_relat_1(sK7) = k9_relat_1(sK7,sK4)
    | ~ v1_relat_1(sK7)
    | ~ spl8_5 ),
    inference(superposition,[],[f59,f167])).

fof(f59,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f478,plain,
    ( k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f476])).

fof(f476,plain,
    ( spl8_41
  <=> k2_relat_1(sK6) = k10_relat_1(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f495,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f493,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f40])).

fof(f493,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_6 ),
    inference(resolution,[],[f171,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f171,plain,
    ( sP0(sK4,sK5)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_6
  <=> sP0(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f487,plain,(
    spl8_42 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | spl8_42 ),
    inference(subsumption_resolution,[],[f485,f90])).

fof(f90,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f68,f51])).

fof(f485,plain,
    ( ~ v1_relat_1(sK6)
    | spl8_42 ),
    inference(subsumption_resolution,[],[f484,f99])).

fof(f99,plain,(
    v5_relat_1(sK6,sK4) ),
    inference(resolution,[],[f72,f51])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f484,plain,
    ( ~ v5_relat_1(sK6,sK4)
    | ~ v1_relat_1(sK6)
    | spl8_42 ),
    inference(resolution,[],[f482,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f482,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK4)
    | spl8_42 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl8_42
  <=> r1_tarski(k2_relat_1(sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f483,plain,
    ( spl8_41
    | ~ spl8_42
    | ~ spl8_5
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f474,f218,f165,f480,f476])).

fof(f218,plain,
    ( spl8_10
  <=> sK5 = k2_relat_1(k5_relat_1(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f474,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK4)
    | k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ spl8_5
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f473,f167])).

fof(f473,plain,
    ( k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7))
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f472,f91])).

fof(f472,plain,
    ( k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f471,f52])).

fof(f471,plain,
    ( k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f467,f56])).

fof(f467,plain,
    ( k2_relat_1(sK6) = k10_relat_1(sK7,sK5)
    | ~ v2_funct_1(sK7)
    | ~ r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_10 ),
    inference(superposition,[],[f64,f325])).

fof(f325,plain,
    ( sK5 = k9_relat_1(sK7,k2_relat_1(sK6))
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f324,f90])).

fof(f324,plain,
    ( sK5 = k9_relat_1(sK7,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f311,f91])).

fof(f311,plain,
    ( sK5 = k9_relat_1(sK7,k2_relat_1(sK6))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | ~ spl8_10 ),
    inference(superposition,[],[f220,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f220,plain,
    ( sK5 = k2_relat_1(k5_relat_1(sK6,sK7))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f218])).

fof(f437,plain,
    ( spl8_37
    | ~ spl8_10
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f436,f386,f218,f390])).

fof(f386,plain,
    ( spl8_36
  <=> r1_tarski(k2_relat_1(sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f436,plain,
    ( sK5 = k2_relat_1(sK7)
    | ~ spl8_10
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f435,f329])).

fof(f329,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7))
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f328,f90])).

fof(f328,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7))
    | ~ v1_relat_1(sK6)
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f313,f91])).

fof(f313,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | ~ spl8_10 ),
    inference(superposition,[],[f60,f220])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f435,plain,
    ( sK5 = k2_relat_1(sK7)
    | ~ r1_tarski(sK5,k2_relat_1(sK7))
    | ~ spl8_36 ),
    inference(resolution,[],[f387,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f387,plain,
    ( r1_tarski(k2_relat_1(sK7),sK5)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f386])).

fof(f433,plain,
    ( spl8_9
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f432,f120,f214])).

fof(f214,plain,
    ( spl8_9
  <=> m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f120,plain,
    ( spl8_1
  <=> m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f432,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f431,f49])).

fof(f49,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f431,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f430,f51])).

fof(f430,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f429,f52])).

fof(f429,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f406,f54])).

fof(f406,plain,
    ( m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_1 ),
    inference(superposition,[],[f121,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f121,plain,
    ( m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f398,plain,(
    spl8_36 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | spl8_36 ),
    inference(subsumption_resolution,[],[f396,f91])).

fof(f396,plain,
    ( ~ v1_relat_1(sK7)
    | spl8_36 ),
    inference(subsumption_resolution,[],[f395,f100])).

fof(f100,plain,(
    v5_relat_1(sK7,sK5) ),
    inference(resolution,[],[f72,f54])).

fof(f395,plain,
    ( ~ v5_relat_1(sK7,sK5)
    | ~ v1_relat_1(sK7)
    | spl8_36 ),
    inference(resolution,[],[f388,f62])).

fof(f388,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK5)
    | spl8_36 ),
    inference(avatar_component_clause,[],[f386])).

fof(f240,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f238,f49])).

fof(f238,plain,
    ( ~ v1_funct_1(sK6)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f237,f51])).

fof(f237,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f236,f52])).

fof(f236,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f226,f54])).

fof(f226,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6)
    | spl8_1 ),
    inference(resolution,[],[f83,f122])).

fof(f122,plain,
    ( ~ m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f222,plain,
    ( ~ spl8_9
    | spl8_10 ),
    inference(avatar_split_clause,[],[f212,f218,f214])).

fof(f212,plain,
    ( sK5 = k2_relat_1(k5_relat_1(sK6,sK7))
    | ~ m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(superposition,[],[f70,f208])).

fof(f208,plain,(
    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f207,f49])).

fof(f207,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f206,f51])).

fof(f206,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f205,f52])).

fof(f205,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f198,f54])).

fof(f198,plain,
    ( sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK6) ),
    inference(superposition,[],[f55,f81])).

fof(f55,plain,(
    sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f40])).

fof(f172,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f163,f169,f165])).

fof(f163,plain,
    ( sP0(sK4,sK5)
    | sK4 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f152,f53])).

fof(f53,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f152,plain,
    ( ~ v1_funct_2(sK7,sK4,sK5)
    | sP0(sK4,sK5)
    | sK4 = k1_relat_1(sK7) ),
    inference(resolution,[],[f145,f54])).

fof(f145,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f143,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f29,f36,f35,f34])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f143,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f75,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 16:56:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.17/0.41  % (5757)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.17/0.42  % (5749)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.17/0.45  % (5758)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.17/0.46  % (5750)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.17/0.46  % (5766)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.17/0.46  % (5764)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.17/0.46  % (5747)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.17/0.47  % (5747)Refutation found. Thanks to Tanya!
% 0.17/0.47  % SZS status Theorem for theBenchmark
% 0.17/0.47  % SZS output start Proof for theBenchmark
% 0.17/0.47  fof(f542,plain,(
% 0.17/0.47    $false),
% 0.17/0.47    inference(avatar_sat_refutation,[],[f172,f222,f240,f398,f433,f437,f483,f487,f495,f541])).
% 0.17/0.47  fof(f541,plain,(
% 0.17/0.47    ~spl8_5 | ~spl8_37 | ~spl8_41),
% 0.17/0.47    inference(avatar_contradiction_clause,[],[f540])).
% 0.17/0.47  fof(f540,plain,(
% 0.17/0.47    $false | (~spl8_5 | ~spl8_37 | ~spl8_41)),
% 0.17/0.47    inference(subsumption_resolution,[],[f539,f128])).
% 0.17/0.47  fof(f128,plain,(
% 0.17/0.47    sK4 != k2_relat_1(sK6)),
% 0.17/0.47    inference(subsumption_resolution,[],[f117,f51])).
% 0.17/0.47  fof(f51,plain,(
% 0.17/0.47    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.17/0.47    inference(cnf_transformation,[],[f40])).
% 0.17/0.47  fof(f40,plain,(
% 0.17/0.47    (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(sK7) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 0.17/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f17,f39,f38])).
% 0.17/0.47  fof(f38,plain,(
% 0.17/0.47    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(X4) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X4,sK4,sK5) & v1_funct_1(X4)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.17/0.47    introduced(choice_axiom,[])).
% 0.17/0.47  fof(f39,plain,(
% 0.17/0.47    ? [X4] : (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(X4) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X4,sK4,sK5) & v1_funct_1(X4)) => (sK4 != k2_relset_1(sK3,sK4,sK6) & k1_xboole_0 != sK5 & v2_funct_1(sK7) & sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 0.17/0.47    introduced(choice_axiom,[])).
% 0.17/0.47  fof(f17,plain,(
% 0.17/0.47    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.17/0.47    inference(flattening,[],[f16])).
% 0.17/0.47  fof(f16,plain,(
% 0.17/0.47    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.17/0.47    inference(ennf_transformation,[],[f15])).
% 0.17/0.47  fof(f15,negated_conjecture,(
% 0.17/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.17/0.47    inference(negated_conjecture,[],[f14])).
% 0.17/0.47  fof(f14,conjecture,(
% 0.17/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 0.17/0.47  fof(f117,plain,(
% 0.17/0.47    sK4 != k2_relat_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.17/0.47    inference(superposition,[],[f58,f70])).
% 0.17/0.47  fof(f70,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.17/0.47    inference(cnf_transformation,[],[f26])).
% 0.17/0.47  fof(f26,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(ennf_transformation,[],[f10])).
% 0.17/0.47  fof(f10,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.17/0.47  fof(f58,plain,(
% 0.17/0.47    sK4 != k2_relset_1(sK3,sK4,sK6)),
% 0.17/0.47    inference(cnf_transformation,[],[f40])).
% 0.17/0.47  fof(f539,plain,(
% 0.17/0.47    sK4 = k2_relat_1(sK6) | (~spl8_5 | ~spl8_37 | ~spl8_41)),
% 0.17/0.47    inference(backward_demodulation,[],[f478,f525])).
% 0.17/0.47  fof(f525,plain,(
% 0.17/0.47    sK4 = k10_relat_1(sK7,sK5) | (~spl8_5 | ~spl8_37)),
% 0.17/0.47    inference(subsumption_resolution,[],[f524,f84])).
% 0.17/0.47  fof(f84,plain,(
% 0.17/0.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.17/0.47    inference(equality_resolution,[],[f66])).
% 0.17/0.47  fof(f66,plain,(
% 0.17/0.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.17/0.47    inference(cnf_transformation,[],[f43])).
% 0.17/0.47  fof(f43,plain,(
% 0.17/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.47    inference(flattening,[],[f42])).
% 0.17/0.47  fof(f42,plain,(
% 0.17/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.17/0.47    inference(nnf_transformation,[],[f1])).
% 0.17/0.47  fof(f1,axiom,(
% 0.17/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.17/0.47  fof(f524,plain,(
% 0.17/0.47    ~r1_tarski(sK4,sK4) | sK4 = k10_relat_1(sK7,sK5) | (~spl8_5 | ~spl8_37)),
% 0.17/0.47    inference(forward_demodulation,[],[f523,f167])).
% 0.17/0.47  fof(f167,plain,(
% 0.17/0.47    sK4 = k1_relat_1(sK7) | ~spl8_5),
% 0.17/0.47    inference(avatar_component_clause,[],[f165])).
% 0.17/0.47  fof(f165,plain,(
% 0.17/0.47    spl8_5 <=> sK4 = k1_relat_1(sK7)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.17/0.47  fof(f523,plain,(
% 0.17/0.47    sK4 = k10_relat_1(sK7,sK5) | ~r1_tarski(sK4,k1_relat_1(sK7)) | (~spl8_5 | ~spl8_37)),
% 0.17/0.47    inference(subsumption_resolution,[],[f522,f91])).
% 0.17/0.47  fof(f91,plain,(
% 0.17/0.47    v1_relat_1(sK7)),
% 0.17/0.47    inference(resolution,[],[f68,f54])).
% 0.17/0.47  fof(f54,plain,(
% 0.17/0.47    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.17/0.47    inference(cnf_transformation,[],[f40])).
% 0.17/0.47  fof(f68,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f24])).
% 0.17/0.47  fof(f24,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(ennf_transformation,[],[f7])).
% 0.17/0.47  fof(f7,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.17/0.47  fof(f522,plain,(
% 0.17/0.47    sK4 = k10_relat_1(sK7,sK5) | ~r1_tarski(sK4,k1_relat_1(sK7)) | ~v1_relat_1(sK7) | (~spl8_5 | ~spl8_37)),
% 0.17/0.47    inference(subsumption_resolution,[],[f521,f52])).
% 0.17/0.47  fof(f52,plain,(
% 0.17/0.47    v1_funct_1(sK7)),
% 0.17/0.47    inference(cnf_transformation,[],[f40])).
% 0.17/0.47  fof(f521,plain,(
% 0.17/0.47    sK4 = k10_relat_1(sK7,sK5) | ~r1_tarski(sK4,k1_relat_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | (~spl8_5 | ~spl8_37)),
% 0.17/0.47    inference(subsumption_resolution,[],[f520,f56])).
% 0.17/0.47  fof(f56,plain,(
% 0.17/0.47    v2_funct_1(sK7)),
% 0.17/0.47    inference(cnf_transformation,[],[f40])).
% 0.17/0.47  fof(f520,plain,(
% 0.17/0.47    sK4 = k10_relat_1(sK7,sK5) | ~v2_funct_1(sK7) | ~r1_tarski(sK4,k1_relat_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | (~spl8_5 | ~spl8_37)),
% 0.17/0.47    inference(superposition,[],[f64,f512])).
% 0.17/0.47  fof(f512,plain,(
% 0.17/0.47    sK5 = k9_relat_1(sK7,sK4) | (~spl8_5 | ~spl8_37)),
% 0.17/0.47    inference(forward_demodulation,[],[f511,f392])).
% 0.17/0.47  fof(f392,plain,(
% 0.17/0.47    sK5 = k2_relat_1(sK7) | ~spl8_37),
% 0.17/0.47    inference(avatar_component_clause,[],[f390])).
% 0.17/0.47  fof(f390,plain,(
% 0.17/0.47    spl8_37 <=> sK5 = k2_relat_1(sK7)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.17/0.47  fof(f511,plain,(
% 0.17/0.47    k2_relat_1(sK7) = k9_relat_1(sK7,sK4) | ~spl8_5),
% 0.17/0.47    inference(subsumption_resolution,[],[f510,f91])).
% 0.17/0.47  fof(f510,plain,(
% 0.17/0.47    k2_relat_1(sK7) = k9_relat_1(sK7,sK4) | ~v1_relat_1(sK7) | ~spl8_5),
% 0.17/0.47    inference(superposition,[],[f59,f167])).
% 0.17/0.47  fof(f59,plain,(
% 0.17/0.47    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f18])).
% 0.17/0.47  fof(f18,plain,(
% 0.17/0.47    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.17/0.47    inference(ennf_transformation,[],[f3])).
% 0.17/0.47  fof(f3,axiom,(
% 0.17/0.47    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.17/0.47  fof(f64,plain,(
% 0.17/0.47    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f23])).
% 0.17/0.47  fof(f23,plain,(
% 0.17/0.47    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.17/0.47    inference(flattening,[],[f22])).
% 0.17/0.47  fof(f22,plain,(
% 0.17/0.47    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.17/0.47    inference(ennf_transformation,[],[f6])).
% 0.17/0.47  fof(f6,axiom,(
% 0.17/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.17/0.47  fof(f478,plain,(
% 0.17/0.47    k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | ~spl8_41),
% 0.17/0.47    inference(avatar_component_clause,[],[f476])).
% 0.17/0.47  fof(f476,plain,(
% 0.17/0.47    spl8_41 <=> k2_relat_1(sK6) = k10_relat_1(sK7,sK5)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 0.17/0.47  fof(f495,plain,(
% 0.17/0.47    ~spl8_6),
% 0.17/0.47    inference(avatar_contradiction_clause,[],[f494])).
% 0.17/0.47  fof(f494,plain,(
% 0.17/0.47    $false | ~spl8_6),
% 0.17/0.47    inference(subsumption_resolution,[],[f493,f57])).
% 0.17/0.47  fof(f57,plain,(
% 0.17/0.47    k1_xboole_0 != sK5),
% 0.17/0.47    inference(cnf_transformation,[],[f40])).
% 0.17/0.47  fof(f493,plain,(
% 0.17/0.47    k1_xboole_0 = sK5 | ~spl8_6),
% 0.17/0.47    inference(resolution,[],[f171,f77])).
% 0.17/0.47  fof(f77,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.17/0.47    inference(cnf_transformation,[],[f48])).
% 0.17/0.47  fof(f48,plain,(
% 0.17/0.47    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.17/0.47    inference(nnf_transformation,[],[f34])).
% 0.17/0.47  fof(f34,plain,(
% 0.17/0.47    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.17/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.17/0.47  fof(f171,plain,(
% 0.17/0.47    sP0(sK4,sK5) | ~spl8_6),
% 0.17/0.47    inference(avatar_component_clause,[],[f169])).
% 0.17/0.47  fof(f169,plain,(
% 0.17/0.47    spl8_6 <=> sP0(sK4,sK5)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.17/0.47  fof(f487,plain,(
% 0.17/0.47    spl8_42),
% 0.17/0.47    inference(avatar_contradiction_clause,[],[f486])).
% 0.17/0.47  fof(f486,plain,(
% 0.17/0.47    $false | spl8_42),
% 0.17/0.47    inference(subsumption_resolution,[],[f485,f90])).
% 0.17/0.47  fof(f90,plain,(
% 0.17/0.47    v1_relat_1(sK6)),
% 0.17/0.47    inference(resolution,[],[f68,f51])).
% 0.17/0.47  fof(f485,plain,(
% 0.17/0.47    ~v1_relat_1(sK6) | spl8_42),
% 0.17/0.47    inference(subsumption_resolution,[],[f484,f99])).
% 0.17/0.47  fof(f99,plain,(
% 0.17/0.47    v5_relat_1(sK6,sK4)),
% 0.17/0.47    inference(resolution,[],[f72,f51])).
% 0.17/0.47  fof(f72,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f27])).
% 0.17/0.47  fof(f27,plain,(
% 0.17/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(ennf_transformation,[],[f8])).
% 0.17/0.47  fof(f8,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.17/0.47  fof(f484,plain,(
% 0.17/0.47    ~v5_relat_1(sK6,sK4) | ~v1_relat_1(sK6) | spl8_42),
% 0.17/0.47    inference(resolution,[],[f482,f62])).
% 0.17/0.47  fof(f62,plain,(
% 0.17/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f41])).
% 0.17/0.47  fof(f41,plain,(
% 0.17/0.47    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.17/0.47    inference(nnf_transformation,[],[f21])).
% 0.17/0.47  fof(f21,plain,(
% 0.17/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.17/0.47    inference(ennf_transformation,[],[f2])).
% 0.17/0.47  fof(f2,axiom,(
% 0.17/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.17/0.47  fof(f482,plain,(
% 0.17/0.47    ~r1_tarski(k2_relat_1(sK6),sK4) | spl8_42),
% 0.17/0.47    inference(avatar_component_clause,[],[f480])).
% 0.17/0.47  fof(f480,plain,(
% 0.17/0.47    spl8_42 <=> r1_tarski(k2_relat_1(sK6),sK4)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 0.17/0.47  fof(f483,plain,(
% 0.17/0.47    spl8_41 | ~spl8_42 | ~spl8_5 | ~spl8_10),
% 0.17/0.47    inference(avatar_split_clause,[],[f474,f218,f165,f480,f476])).
% 0.17/0.47  fof(f218,plain,(
% 0.17/0.47    spl8_10 <=> sK5 = k2_relat_1(k5_relat_1(sK6,sK7))),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.17/0.47  fof(f474,plain,(
% 0.17/0.47    ~r1_tarski(k2_relat_1(sK6),sK4) | k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | (~spl8_5 | ~spl8_10)),
% 0.17/0.47    inference(forward_demodulation,[],[f473,f167])).
% 0.17/0.47  fof(f473,plain,(
% 0.17/0.47    k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | ~r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) | ~spl8_10),
% 0.17/0.47    inference(subsumption_resolution,[],[f472,f91])).
% 0.17/0.47  fof(f472,plain,(
% 0.17/0.47    k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | ~r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) | ~v1_relat_1(sK7) | ~spl8_10),
% 0.17/0.47    inference(subsumption_resolution,[],[f471,f52])).
% 0.17/0.47  fof(f471,plain,(
% 0.17/0.47    k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | ~r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl8_10),
% 0.17/0.47    inference(subsumption_resolution,[],[f467,f56])).
% 0.17/0.47  fof(f467,plain,(
% 0.17/0.47    k2_relat_1(sK6) = k10_relat_1(sK7,sK5) | ~v2_funct_1(sK7) | ~r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl8_10),
% 0.17/0.47    inference(superposition,[],[f64,f325])).
% 0.17/0.47  fof(f325,plain,(
% 0.17/0.47    sK5 = k9_relat_1(sK7,k2_relat_1(sK6)) | ~spl8_10),
% 0.17/0.47    inference(subsumption_resolution,[],[f324,f90])).
% 0.17/0.47  fof(f324,plain,(
% 0.17/0.47    sK5 = k9_relat_1(sK7,k2_relat_1(sK6)) | ~v1_relat_1(sK6) | ~spl8_10),
% 0.17/0.47    inference(subsumption_resolution,[],[f311,f91])).
% 0.17/0.47  fof(f311,plain,(
% 0.17/0.47    sK5 = k9_relat_1(sK7,k2_relat_1(sK6)) | ~v1_relat_1(sK7) | ~v1_relat_1(sK6) | ~spl8_10),
% 0.17/0.47    inference(superposition,[],[f220,f61])).
% 0.17/0.47  fof(f61,plain,(
% 0.17/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f20])).
% 0.17/0.47  fof(f20,plain,(
% 0.17/0.47    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.17/0.47    inference(ennf_transformation,[],[f4])).
% 0.17/0.47  fof(f4,axiom,(
% 0.17/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.17/0.47  fof(f220,plain,(
% 0.17/0.47    sK5 = k2_relat_1(k5_relat_1(sK6,sK7)) | ~spl8_10),
% 0.17/0.47    inference(avatar_component_clause,[],[f218])).
% 0.17/0.47  fof(f437,plain,(
% 0.17/0.47    spl8_37 | ~spl8_10 | ~spl8_36),
% 0.17/0.47    inference(avatar_split_clause,[],[f436,f386,f218,f390])).
% 0.17/0.47  fof(f386,plain,(
% 0.17/0.47    spl8_36 <=> r1_tarski(k2_relat_1(sK7),sK5)),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.17/0.47  fof(f436,plain,(
% 0.17/0.47    sK5 = k2_relat_1(sK7) | (~spl8_10 | ~spl8_36)),
% 0.17/0.47    inference(subsumption_resolution,[],[f435,f329])).
% 0.17/0.47  fof(f329,plain,(
% 0.17/0.47    r1_tarski(sK5,k2_relat_1(sK7)) | ~spl8_10),
% 0.17/0.47    inference(subsumption_resolution,[],[f328,f90])).
% 0.17/0.47  fof(f328,plain,(
% 0.17/0.47    r1_tarski(sK5,k2_relat_1(sK7)) | ~v1_relat_1(sK6) | ~spl8_10),
% 0.17/0.47    inference(subsumption_resolution,[],[f313,f91])).
% 0.17/0.47  fof(f313,plain,(
% 0.17/0.47    r1_tarski(sK5,k2_relat_1(sK7)) | ~v1_relat_1(sK7) | ~v1_relat_1(sK6) | ~spl8_10),
% 0.17/0.47    inference(superposition,[],[f60,f220])).
% 0.17/0.47  fof(f60,plain,(
% 0.17/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f19])).
% 0.17/0.47  fof(f19,plain,(
% 0.17/0.47    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.17/0.47    inference(ennf_transformation,[],[f5])).
% 0.17/0.47  fof(f5,axiom,(
% 0.17/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.17/0.47  fof(f435,plain,(
% 0.17/0.47    sK5 = k2_relat_1(sK7) | ~r1_tarski(sK5,k2_relat_1(sK7)) | ~spl8_36),
% 0.17/0.47    inference(resolution,[],[f387,f67])).
% 0.17/0.47  fof(f67,plain,(
% 0.17/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f43])).
% 0.17/0.47  fof(f387,plain,(
% 0.17/0.47    r1_tarski(k2_relat_1(sK7),sK5) | ~spl8_36),
% 0.17/0.47    inference(avatar_component_clause,[],[f386])).
% 0.17/0.47  fof(f433,plain,(
% 0.17/0.47    spl8_9 | ~spl8_1),
% 0.17/0.47    inference(avatar_split_clause,[],[f432,f120,f214])).
% 0.17/0.47  fof(f214,plain,(
% 0.17/0.47    spl8_9 <=> m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.17/0.47  fof(f120,plain,(
% 0.17/0.47    spl8_1 <=> m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 0.17/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.17/0.47  fof(f432,plain,(
% 0.17/0.47    m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~spl8_1),
% 0.17/0.47    inference(subsumption_resolution,[],[f431,f49])).
% 0.17/0.47  fof(f49,plain,(
% 0.17/0.47    v1_funct_1(sK6)),
% 0.17/0.47    inference(cnf_transformation,[],[f40])).
% 0.17/0.47  fof(f431,plain,(
% 0.17/0.47    m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_1(sK6) | ~spl8_1),
% 0.17/0.47    inference(subsumption_resolution,[],[f430,f51])).
% 0.17/0.47  fof(f430,plain,(
% 0.17/0.47    m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | ~spl8_1),
% 0.17/0.47    inference(subsumption_resolution,[],[f429,f52])).
% 0.17/0.47  fof(f429,plain,(
% 0.17/0.47    m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | ~spl8_1),
% 0.17/0.47    inference(subsumption_resolution,[],[f406,f54])).
% 0.17/0.47  fof(f406,plain,(
% 0.17/0.47    m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | ~spl8_1),
% 0.17/0.47    inference(superposition,[],[f121,f81])).
% 0.17/0.47  fof(f81,plain,(
% 0.17/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f31])).
% 0.17/0.47  fof(f31,plain,(
% 0.17/0.47    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.17/0.47    inference(flattening,[],[f30])).
% 0.17/0.47  fof(f30,plain,(
% 0.17/0.47    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.17/0.47    inference(ennf_transformation,[],[f13])).
% 0.17/0.47  fof(f13,axiom,(
% 0.17/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.17/0.47  fof(f121,plain,(
% 0.17/0.47    m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~spl8_1),
% 0.17/0.47    inference(avatar_component_clause,[],[f120])).
% 0.17/0.47  fof(f398,plain,(
% 0.17/0.47    spl8_36),
% 0.17/0.47    inference(avatar_contradiction_clause,[],[f397])).
% 0.17/0.47  fof(f397,plain,(
% 0.17/0.47    $false | spl8_36),
% 0.17/0.47    inference(subsumption_resolution,[],[f396,f91])).
% 0.17/0.47  fof(f396,plain,(
% 0.17/0.47    ~v1_relat_1(sK7) | spl8_36),
% 0.17/0.47    inference(subsumption_resolution,[],[f395,f100])).
% 0.17/0.47  fof(f100,plain,(
% 0.17/0.47    v5_relat_1(sK7,sK5)),
% 0.17/0.47    inference(resolution,[],[f72,f54])).
% 0.17/0.47  fof(f395,plain,(
% 0.17/0.47    ~v5_relat_1(sK7,sK5) | ~v1_relat_1(sK7) | spl8_36),
% 0.17/0.47    inference(resolution,[],[f388,f62])).
% 0.17/0.47  fof(f388,plain,(
% 0.17/0.47    ~r1_tarski(k2_relat_1(sK7),sK5) | spl8_36),
% 0.17/0.47    inference(avatar_component_clause,[],[f386])).
% 0.17/0.47  fof(f240,plain,(
% 0.17/0.47    spl8_1),
% 0.17/0.47    inference(avatar_contradiction_clause,[],[f239])).
% 0.17/0.47  fof(f239,plain,(
% 0.17/0.47    $false | spl8_1),
% 0.17/0.47    inference(subsumption_resolution,[],[f238,f49])).
% 0.17/0.47  fof(f238,plain,(
% 0.17/0.47    ~v1_funct_1(sK6) | spl8_1),
% 0.17/0.47    inference(subsumption_resolution,[],[f237,f51])).
% 0.17/0.47  fof(f237,plain,(
% 0.17/0.47    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | spl8_1),
% 0.17/0.47    inference(subsumption_resolution,[],[f236,f52])).
% 0.17/0.47  fof(f236,plain,(
% 0.17/0.47    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | spl8_1),
% 0.17/0.47    inference(subsumption_resolution,[],[f226,f54])).
% 0.17/0.47  fof(f226,plain,(
% 0.17/0.47    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6) | spl8_1),
% 0.17/0.47    inference(resolution,[],[f83,f122])).
% 0.17/0.47  fof(f122,plain,(
% 0.17/0.47    ~m1_subset_1(k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | spl8_1),
% 0.17/0.47    inference(avatar_component_clause,[],[f120])).
% 0.17/0.47  fof(f83,plain,(
% 0.17/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f33])).
% 0.17/0.47  fof(f33,plain,(
% 0.17/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.17/0.47    inference(flattening,[],[f32])).
% 0.17/0.47  fof(f32,plain,(
% 0.17/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.17/0.47    inference(ennf_transformation,[],[f12])).
% 0.17/0.47  fof(f12,axiom,(
% 0.17/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.17/0.47  fof(f222,plain,(
% 0.17/0.47    ~spl8_9 | spl8_10),
% 0.17/0.47    inference(avatar_split_clause,[],[f212,f218,f214])).
% 0.17/0.47  fof(f212,plain,(
% 0.17/0.47    sK5 = k2_relat_1(k5_relat_1(sK6,sK7)) | ~m1_subset_1(k5_relat_1(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 0.17/0.47    inference(superposition,[],[f70,f208])).
% 0.17/0.47  fof(f208,plain,(
% 0.17/0.47    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7))),
% 0.17/0.47    inference(subsumption_resolution,[],[f207,f49])).
% 0.17/0.47  fof(f207,plain,(
% 0.17/0.47    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~v1_funct_1(sK6)),
% 0.17/0.47    inference(subsumption_resolution,[],[f206,f51])).
% 0.17/0.47  fof(f206,plain,(
% 0.17/0.47    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)),
% 0.17/0.47    inference(subsumption_resolution,[],[f205,f52])).
% 0.17/0.47  fof(f205,plain,(
% 0.17/0.47    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)),
% 0.17/0.47    inference(subsumption_resolution,[],[f198,f54])).
% 0.17/0.47  fof(f198,plain,(
% 0.17/0.47    sK5 = k2_relset_1(sK3,sK5,k5_relat_1(sK6,sK7)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_1(sK6)),
% 0.17/0.47    inference(superposition,[],[f55,f81])).
% 0.17/0.47  fof(f55,plain,(
% 0.17/0.47    sK5 = k2_relset_1(sK3,sK5,k1_partfun1(sK3,sK4,sK4,sK5,sK6,sK7))),
% 0.17/0.47    inference(cnf_transformation,[],[f40])).
% 0.17/0.47  fof(f172,plain,(
% 0.17/0.47    spl8_5 | spl8_6),
% 0.17/0.47    inference(avatar_split_clause,[],[f163,f169,f165])).
% 0.17/0.47  fof(f163,plain,(
% 0.17/0.47    sP0(sK4,sK5) | sK4 = k1_relat_1(sK7)),
% 0.17/0.47    inference(subsumption_resolution,[],[f152,f53])).
% 0.17/0.47  fof(f53,plain,(
% 0.17/0.47    v1_funct_2(sK7,sK4,sK5)),
% 0.17/0.47    inference(cnf_transformation,[],[f40])).
% 0.17/0.47  fof(f152,plain,(
% 0.17/0.47    ~v1_funct_2(sK7,sK4,sK5) | sP0(sK4,sK5) | sK4 = k1_relat_1(sK7)),
% 0.17/0.47    inference(resolution,[],[f145,f54])).
% 0.17/0.47  fof(f145,plain,(
% 0.17/0.47    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.17/0.47    inference(subsumption_resolution,[],[f143,f79])).
% 0.17/0.47  fof(f79,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f37])).
% 0.17/0.47  fof(f37,plain,(
% 0.17/0.47    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(definition_folding,[],[f29,f36,f35,f34])).
% 0.17/0.47  fof(f35,plain,(
% 0.17/0.47    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.17/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.17/0.47  fof(f36,plain,(
% 0.17/0.47    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.17/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.17/0.47  fof(f29,plain,(
% 0.17/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(flattening,[],[f28])).
% 0.17/0.47  fof(f28,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(ennf_transformation,[],[f11])).
% 0.17/0.47  fof(f11,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.17/0.47  fof(f143,plain,(
% 0.17/0.47    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.17/0.47    inference(superposition,[],[f75,f69])).
% 0.17/0.47  fof(f69,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.17/0.47    inference(cnf_transformation,[],[f25])).
% 0.17/0.47  fof(f25,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.17/0.47    inference(ennf_transformation,[],[f9])).
% 0.17/0.47  fof(f9,axiom,(
% 0.17/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.17/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.17/0.47  fof(f75,plain,(
% 0.17/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.17/0.47    inference(cnf_transformation,[],[f47])).
% 0.17/0.47  fof(f47,plain,(
% 0.17/0.47    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.17/0.47    inference(rectify,[],[f46])).
% 0.17/0.47  fof(f46,plain,(
% 0.17/0.47    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.17/0.47    inference(nnf_transformation,[],[f35])).
% 0.17/0.47  % SZS output end Proof for theBenchmark
% 0.17/0.47  % (5747)------------------------------
% 0.17/0.47  % (5747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.47  % (5747)Termination reason: Refutation
% 0.17/0.47  
% 0.17/0.47  % (5747)Memory used [KB]: 6396
% 0.17/0.47  % (5747)Time elapsed: 0.097 s
% 0.17/0.47  % (5747)------------------------------
% 0.17/0.47  % (5747)------------------------------
% 0.17/0.47  % (5745)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.17/0.47  % (5744)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.17/0.47  % (5756)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.17/0.47  % (5754)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.17/0.48  % (5746)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.17/0.48  % (5768)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.17/0.48  % (5761)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.17/0.48  % (5742)Success in time 0.153 s
%------------------------------------------------------------------------------
