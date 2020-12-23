%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 818 expanded)
%              Number of leaves         :   24 ( 198 expanded)
%              Depth                    :   19
%              Number of atoms          :  609 (4079 expanded)
%              Number of equality atoms :  107 (1055 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f979,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f98,f120,f162,f628,f762,f859,f880,f944,f976])).

fof(f976,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f975])).

fof(f975,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f974,f955])).

fof(f955,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f950,f76])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f950,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f116,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f116,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f59,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f974,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f961,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f961,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,k1_xboole_0))
    | spl4_3
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f875,f673])).

fof(f673,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f875,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK2,sK1))
    | spl4_3 ),
    inference(resolution,[],[f869,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f869,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(subsumption_resolution,[],[f866,f43])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f866,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(resolution,[],[f864,f191])).

fof(f191,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f74,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f864,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(subsumption_resolution,[],[f863,f43])).

fof(f863,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f862,f45])).

fof(f862,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(superposition,[],[f90,f72])).

fof(f90,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f944,plain,
    ( spl4_29
    | spl4_4 ),
    inference(avatar_split_clause,[],[f943,f93,f671])).

fof(f671,plain,
    ( spl4_29
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f943,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f767,f44])).

fof(f44,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f767,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f45,f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f880,plain,
    ( spl4_3
    | ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f879])).

fof(f879,plain,
    ( $false
    | spl4_3
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f878,f335])).

fof(f335,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f334,f43])).

fof(f334,plain,(
    ! [X0] :
      ( v1_relat_1(k7_relat_1(sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f333,f45])).

fof(f333,plain,(
    ! [X0] :
      ( v1_relat_1(k7_relat_1(sK3,X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f321,f72])).

fof(f321,plain,(
    ! [X0] : v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f313,f43])).

fof(f313,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0)) ) ),
    inference(resolution,[],[f193,f45])).

fof(f193,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X9)
      | v1_relat_1(k2_partfun1(X10,X11,X9,X12)) ) ),
    inference(subsumption_resolution,[],[f186,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f186,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X9)
      | v1_relat_1(k2_partfun1(X10,X11,X9,X12))
      | ~ v1_relat_1(k2_zfmisc_1(X10,X11)) ) ),
    inference(resolution,[],[f74,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f878,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_3
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f876,f644])).

fof(f644,plain,(
    ! [X21] : v5_relat_1(k7_relat_1(sK3,X21),sK1) ),
    inference(subsumption_resolution,[],[f636,f43])).

fof(f636,plain,(
    ! [X21] :
      ( ~ v1_funct_1(sK3)
      | v5_relat_1(k7_relat_1(sK3,X21),sK1) ) ),
    inference(resolution,[],[f332,f45])).

fof(f332,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v5_relat_1(k7_relat_1(X2,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_relat_1(k7_relat_1(X2,X3),X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(superposition,[],[f185,f72])).

fof(f185,plain,(
    ! [X6,X8,X7,X5] :
      ( v5_relat_1(k2_partfun1(X6,X7,X5,X8),X7)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f74,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f876,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_3
    | ~ spl4_29 ),
    inference(resolution,[],[f873,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f873,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_3
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f872,f46])).

fof(f46,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f872,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_3
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f871,f785])).

fof(f785,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f781,f45])).

fof(f781,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_29 ),
    inference(superposition,[],[f672,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f672,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f671])).

fof(f871,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_3 ),
    inference(subsumption_resolution,[],[f870,f123])).

fof(f123,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f121,f51])).

fof(f121,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f49,f45])).

fof(f870,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f867,f181])).

fof(f181,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(subsumption_resolution,[],[f180,f43])).

fof(f180,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f178,f45])).

fof(f178,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK3,X0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f154,f72])).

fof(f154,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f150,f43])).

fof(f150,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f73,f45])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f867,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(resolution,[],[f864,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f174,f142])).

fof(f142,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | v1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f122,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f49,f60])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f58,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f859,plain,
    ( spl4_2
    | ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f858])).

fof(f858,plain,
    ( $false
    | spl4_2
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f857,f46])).

fof(f857,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_2
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f856,f785])).

fof(f856,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f855,f644])).

fof(f855,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f854,f123])).

fof(f854,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f850,f181])).

fof(f850,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | spl4_2 ),
    inference(resolution,[],[f411,f183])).

fof(f183,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f182,f43])).

fof(f182,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f179,f45])).

fof(f179,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_2 ),
    inference(superposition,[],[f87,f72])).

fof(f87,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f411,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k7_relat_1(X0,X1),X1,X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(k7_relat_1(X0,X1),X2) ) ),
    inference(subsumption_resolution,[],[f410,f142])).

fof(f410,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k7_relat_1(X0,X1),X1,X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(k7_relat_1(X0,X1),X2) ) ),
    inference(duplicate_literal_removal,[],[f404])).

fof(f404,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k7_relat_1(X0,X1),X1,X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(k7_relat_1(X0,X1),X2)
      | ~ v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f136,f54])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2)
      | v1_funct_2(k7_relat_1(X0,X1),X1,X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f57,f53])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f762,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | spl4_2
    | ~ spl4_5
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f760,f627])).

fof(f627,plain,
    ( ! [X2] : v1_funct_2(k1_xboole_0,k1_xboole_0,X2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f626])).

fof(f626,plain,
    ( spl4_26
  <=> ! [X2] : v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f760,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f744,f113])).

fof(f113,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f112,f110])).

fof(f110,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f51,f75])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f52,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f744,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f707,f725])).

fof(f725,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(resolution,[],[f684,f50])).

fof(f684,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f679,f76])).

fof(f679,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f116,f97])).

fof(f707,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f183,f704])).

fof(f704,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(resolution,[],[f677,f50])).

fof(f677,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f46,f97])).

fof(f628,plain,
    ( spl4_26
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f624,f104,f626])).

fof(f104,plain,
    ( spl4_7
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f624,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ) ),
    inference(trivial_inequality_removal,[],[f619])).

fof(f619,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ) ),
    inference(superposition,[],[f160,f515])).

fof(f515,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f472,f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(subsumption_resolution,[],[f134,f110])).

fof(f134,plain,(
    ! [X0] :
      ( k1_relat_1(k1_xboole_0) = X0
      | ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f53,f113])).

fof(f472,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f471,f110])).

fof(f471,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f467,f427])).

fof(f427,plain,(
    ! [X0] : v5_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f218,f115])).

fof(f115,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f114,f110])).

fof(f114,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f52,f113])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f131,f60])).

fof(f131,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v5_relat_1(X3,X2) ) ),
    inference(superposition,[],[f65,f76])).

fof(f467,plain,(
    ! [X0] :
      ( ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f230,f422])).

fof(f422,plain,(
    v5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f217,f115])).

fof(f217,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v5_relat_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f130,f60])).

fof(f130,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v5_relat_1(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f65,f75])).

fof(f230,plain,(
    ! [X2,X3] :
      ( ~ v5_relat_1(X2,k1_xboole_0)
      | ~ v5_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | r1_tarski(k1_xboole_0,X3) ) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_xboole_0,X3)
      | ~ v5_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f54,f124])).

fof(f124,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f54,f50])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f158,f76])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f108,f64])).

fof(f108,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f80,f76])).

fof(f80,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f162,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f154,f84])).

fof(f84,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f120,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f117,f115])).

fof(f117,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_7 ),
    inference(resolution,[],[f60,f105])).

fof(f105,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f98,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f47,f96,f93])).

fof(f47,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f48,f89,f86,f83])).

fof(f48,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (29601)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.46  % (29606)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (29611)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (29602)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (29600)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (29607)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (29603)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (29599)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (29610)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (29613)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (29598)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (29599)Refutation not found, incomplete strategy% (29599)------------------------------
% 0.21/0.50  % (29599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29599)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29599)Memory used [KB]: 10618
% 0.21/0.50  % (29599)Time elapsed: 0.084 s
% 0.21/0.50  % (29599)------------------------------
% 0.21/0.50  % (29599)------------------------------
% 0.21/0.50  % (29618)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (29604)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (29600)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (29618)Refutation not found, incomplete strategy% (29618)------------------------------
% 0.21/0.50  % (29618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29618)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  % (29609)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (29616)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (29614)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (29617)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (29612)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (29615)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  
% 0.21/0.51  % (29618)Memory used [KB]: 10618
% 0.21/0.51  % (29618)Time elapsed: 0.075 s
% 0.21/0.51  % (29618)------------------------------
% 0.21/0.51  % (29618)------------------------------
% 0.21/0.51  % (29605)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (29608)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f979,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f91,f98,f120,f162,f628,f762,f859,f880,f944,f976])).
% 0.21/0.52  fof(f976,plain,(
% 0.21/0.52    spl4_3 | ~spl4_4 | ~spl4_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f975])).
% 0.21/0.52  fof(f975,plain,(
% 0.21/0.52    $false | (spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f974,f955])).
% 0.21/0.52  fof(f955,plain,(
% 0.21/0.52    r1_tarski(sK3,k1_xboole_0) | ~spl4_5),
% 0.21/0.52    inference(forward_demodulation,[],[f950,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f950,plain,(
% 0.21/0.52    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl4_5),
% 0.21/0.52    inference(backward_demodulation,[],[f116,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl4_5 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.52    inference(resolution,[],[f59,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f974,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k1_xboole_0) | (spl4_3 | ~spl4_4)),
% 0.21/0.52    inference(forward_demodulation,[],[f961,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f961,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k2_zfmisc_1(sK2,k1_xboole_0)) | (spl4_3 | ~spl4_4)),
% 0.21/0.52    inference(backward_demodulation,[],[f875,f673])).
% 0.21/0.52  fof(f673,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f875,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k2_zfmisc_1(sK2,sK1)) | spl4_3),
% 0.21/0.52    inference(resolution,[],[f869,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f869,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f866,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f866,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK3) | spl4_3),
% 0.21/0.52    inference(resolution,[],[f864,f191])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f188])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(superposition,[],[f74,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.52  fof(f864,plain,(
% 0.21/0.52    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f863,f43])).
% 0.21/0.52  fof(f863,plain,(
% 0.21/0.52    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK3) | spl4_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f862,f45])).
% 0.21/0.52  fof(f862,plain,(
% 0.21/0.52    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_3),
% 0.21/0.52    inference(superposition,[],[f90,f72])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f944,plain,(
% 0.21/0.52    spl4_29 | spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f943,f93,f671])).
% 0.21/0.52  fof(f671,plain,(
% 0.21/0.52    spl4_29 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.52  fof(f943,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f767,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f767,plain,(
% 0.21/0.52    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.52    inference(resolution,[],[f45,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f880,plain,(
% 0.21/0.52    spl4_3 | ~spl4_29),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f879])).
% 0.21/0.52  fof(f879,plain,(
% 0.21/0.52    $false | (spl4_3 | ~spl4_29)),
% 0.21/0.52    inference(subsumption_resolution,[],[f878,f335])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f334,f43])).
% 0.21/0.52  fof(f334,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0)) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f333,f45])).
% 0.21/0.52  fof(f333,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(superposition,[],[f321,f72])).
% 0.21/0.52  fof(f321,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f313,f43])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_1(sK3) | v1_relat_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 0.21/0.52    inference(resolution,[],[f193,f45])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    ( ! [X12,X10,X11,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~v1_funct_1(X9) | v1_relat_1(k2_partfun1(X10,X11,X9,X12))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f186,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ( ! [X12,X10,X11,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~v1_funct_1(X9) | v1_relat_1(k2_partfun1(X10,X11,X9,X12)) | ~v1_relat_1(k2_zfmisc_1(X10,X11))) )),
% 0.21/0.52    inference(resolution,[],[f74,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f878,plain,(
% 0.21/0.52    ~v1_relat_1(k7_relat_1(sK3,sK2)) | (spl4_3 | ~spl4_29)),
% 0.21/0.52    inference(subsumption_resolution,[],[f876,f644])).
% 0.21/0.52  fof(f644,plain,(
% 0.21/0.52    ( ! [X21] : (v5_relat_1(k7_relat_1(sK3,X21),sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f636,f43])).
% 0.21/0.52  fof(f636,plain,(
% 0.21/0.52    ( ! [X21] : (~v1_funct_1(sK3) | v5_relat_1(k7_relat_1(sK3,X21),sK1)) )),
% 0.21/0.52    inference(resolution,[],[f332,f45])).
% 0.21/0.52  fof(f332,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v5_relat_1(k7_relat_1(X2,X3),X1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f331])).
% 0.21/0.52  fof(f331,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v5_relat_1(k7_relat_1(X2,X3),X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(superposition,[],[f185,f72])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X5] : (v5_relat_1(k2_partfun1(X6,X7,X5,X8),X7) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) )),
% 0.21/0.52    inference(resolution,[],[f74,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f876,plain,(
% 0.21/0.52    ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | ~v1_relat_1(k7_relat_1(sK3,sK2)) | (spl4_3 | ~spl4_29)),
% 0.21/0.52    inference(resolution,[],[f873,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.52  fof(f873,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (spl4_3 | ~spl4_29)),
% 0.21/0.52    inference(subsumption_resolution,[],[f872,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    r1_tarski(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f872,plain,(
% 0.21/0.52    ~r1_tarski(sK2,sK0) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (spl4_3 | ~spl4_29)),
% 0.21/0.52    inference(forward_demodulation,[],[f871,f785])).
% 0.21/0.52  fof(f785,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK3) | ~spl4_29),
% 0.21/0.52    inference(subsumption_resolution,[],[f781,f45])).
% 0.21/0.52  fof(f781,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_29),
% 0.21/0.52    inference(superposition,[],[f672,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f672,plain,(
% 0.21/0.52    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f671])).
% 0.21/0.52  fof(f871,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | ~r1_tarski(sK2,k1_relat_1(sK3)) | spl4_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f870,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    v1_relat_1(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f121,f51])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.52    inference(resolution,[],[f49,f45])).
% 0.21/0.52  fof(f870,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f867,f181])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f180,f43])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0)) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f178,f45])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(superposition,[],[f154,f72])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f150,f43])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 0.21/0.52    inference(resolution,[],[f73,f45])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f867,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_3),
% 0.21/0.52    inference(resolution,[],[f864,f177])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f174,f142])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ( ! [X2,X3] : (v1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~v1_relat_1(X2) | v1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(resolution,[],[f122,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f49,f60])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(superposition,[],[f58,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.52  fof(f859,plain,(
% 0.21/0.52    spl4_2 | ~spl4_29),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f858])).
% 0.21/0.52  fof(f858,plain,(
% 0.21/0.52    $false | (spl4_2 | ~spl4_29)),
% 0.21/0.52    inference(subsumption_resolution,[],[f857,f46])).
% 0.21/0.52  fof(f857,plain,(
% 0.21/0.52    ~r1_tarski(sK2,sK0) | (spl4_2 | ~spl4_29)),
% 0.21/0.52    inference(forward_demodulation,[],[f856,f785])).
% 0.21/0.52  fof(f856,plain,(
% 0.21/0.52    ~r1_tarski(sK2,k1_relat_1(sK3)) | spl4_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f855,f644])).
% 0.21/0.52  fof(f855,plain,(
% 0.21/0.52    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | spl4_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f854,f123])).
% 0.21/0.52  fof(f854,plain,(
% 0.21/0.52    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | spl4_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f850,f181])).
% 0.21/0.52  fof(f850,plain,(
% 0.21/0.52    ~v1_funct_1(k7_relat_1(sK3,sK2)) | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | spl4_2),
% 0.21/0.52    inference(resolution,[],[f411,f183])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f182,f43])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_1(sK3) | spl4_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f179,f45])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_2),
% 0.21/0.52    inference(superposition,[],[f87,f72])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f411,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(k7_relat_1(X0,X1),X1,X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v5_relat_1(k7_relat_1(X0,X1),X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f410,f142])).
% 0.21/0.52  fof(f410,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(k7_relat_1(X0,X1),X1,X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v5_relat_1(k7_relat_1(X0,X1),X2)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f404])).
% 0.21/0.52  fof(f404,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(k7_relat_1(X0,X1),X1,X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v5_relat_1(k7_relat_1(X0,X1),X2) | ~v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.21/0.52    inference(resolution,[],[f136,f54])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),X2) | v1_funct_2(k7_relat_1(X0,X1),X1,X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(superposition,[],[f57,f53])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f762,plain,(
% 0.21/0.52    spl4_2 | ~spl4_5 | ~spl4_26),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f761])).
% 0.21/0.52  fof(f761,plain,(
% 0.21/0.52    $false | (spl4_2 | ~spl4_5 | ~spl4_26)),
% 0.21/0.52    inference(subsumption_resolution,[],[f760,f627])).
% 0.21/0.52  fof(f627,plain,(
% 0.21/0.52    ( ! [X2] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) ) | ~spl4_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f626])).
% 0.21/0.52  fof(f626,plain,(
% 0.21/0.52    spl4_26 <=> ! [X2] : v1_funct_2(k1_xboole_0,k1_xboole_0,X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.52  fof(f760,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (spl4_2 | ~spl4_5)),
% 0.21/0.52    inference(forward_demodulation,[],[f744,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f112,f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    v1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f51,f75])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f52,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.52  fof(f744,plain,(
% 0.21/0.52    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1) | (spl4_2 | ~spl4_5)),
% 0.21/0.52    inference(backward_demodulation,[],[f707,f725])).
% 0.21/0.52  fof(f725,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | ~spl4_5),
% 0.21/0.52    inference(resolution,[],[f684,f50])).
% 0.21/0.52  fof(f684,plain,(
% 0.21/0.52    r1_tarski(sK3,k1_xboole_0) | ~spl4_5),
% 0.21/0.52    inference(forward_demodulation,[],[f679,f76])).
% 0.21/0.52  fof(f679,plain,(
% 0.21/0.52    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl4_5),
% 0.21/0.52    inference(backward_demodulation,[],[f116,f97])).
% 0.21/0.52  fof(f707,plain,(
% 0.21/0.52    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | (spl4_2 | ~spl4_5)),
% 0.21/0.52    inference(backward_demodulation,[],[f183,f704])).
% 0.21/0.52  fof(f704,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl4_5),
% 0.21/0.52    inference(resolution,[],[f677,f50])).
% 0.21/0.52  fof(f677,plain,(
% 0.21/0.52    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 0.21/0.52    inference(backward_demodulation,[],[f46,f97])).
% 0.21/0.52  fof(f628,plain,(
% 0.21/0.52    spl4_26 | ~spl4_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f624,f104,f626])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl4_7 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.52  fof(f624,plain,(
% 0.21/0.52    ( ! [X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f619])).
% 0.21/0.52  fof(f619,plain,(
% 0.21/0.52    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) )),
% 0.21/0.52    inference(superposition,[],[f160,f515])).
% 0.21/0.52  fof(f515,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(resolution,[],[f472,f135])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | k1_relat_1(k1_xboole_0) = X0) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f134,f110])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(k1_xboole_0) = X0 | ~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f53,f113])).
% 0.21/0.52  fof(f472,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f471,f110])).
% 0.21/0.52  fof(f471,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f467,f427])).
% 0.21/0.52  fof(f427,plain,(
% 0.21/0.52    ( ! [X0] : (v5_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f218,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f114,f110])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f52,f113])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | v5_relat_1(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f131,f60])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v5_relat_1(X3,X2)) )),
% 0.21/0.52    inference(superposition,[],[f65,f76])).
% 0.21/0.52  fof(f467,plain,(
% 0.21/0.52    ( ! [X0] : (~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f230,f422])).
% 0.21/0.52  fof(f422,plain,(
% 0.21/0.52    v5_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(resolution,[],[f217,f115])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v5_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f130,f60])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v5_relat_1(X1,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f65,f75])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~v5_relat_1(X2,k1_xboole_0) | ~v5_relat_1(X2,X3) | ~v1_relat_1(X2) | r1_tarski(k1_xboole_0,X3)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f228])).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r1_tarski(k1_xboole_0,X3) | ~v5_relat_1(X2,X3) | ~v1_relat_1(X2) | ~v1_relat_1(X2) | ~v5_relat_1(X2,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f54,f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v5_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f54,f50])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f158,f76])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.21/0.52    inference(superposition,[],[f108,f64])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f80,f76])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl4_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    $false | spl4_1),
% 0.21/0.52    inference(resolution,[],[f154,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    spl4_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    $false | spl4_7),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f115])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_7),
% 0.21/0.52    inference(resolution,[],[f60,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f104])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ~spl4_4 | spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f47,f96,f93])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f48,f89,f86,f83])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (29600)------------------------------
% 0.21/0.52  % (29600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29600)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (29600)Memory used [KB]: 11129
% 0.21/0.52  % (29600)Time elapsed: 0.079 s
% 0.21/0.52  % (29600)------------------------------
% 0.21/0.52  % (29600)------------------------------
% 0.21/0.52  % (29595)Success in time 0.165 s
%------------------------------------------------------------------------------
