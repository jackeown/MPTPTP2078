%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 133 expanded)
%              Number of leaves         :   20 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  216 ( 382 expanded)
%              Number of equality atoms :   50 (  88 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f52,f61,f84,f96,f101,f107,f112,f120,f144])).

fof(f144,plain,
    ( spl4_7
    | ~ spl4_12
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f142,f103,f55,f117,f79])).

fof(f79,plain,
    ( spl4_7
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f117,plain,
    ( spl4_12
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f55,plain,
    ( spl4_4
  <=> ! [X0] :
        ( ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK3(X0,k2_relset_1(sK0,sK1,sK2)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f103,plain,
    ( spl4_10
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f142,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(resolution,[],[f121,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1)
        | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0)) )
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f114,f105])).

fof(f105,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1)
        | ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0)) )
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f56,f105])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK3(X0,k2_relset_1(sK0,sK1,sK2)),sK1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f120,plain,
    ( spl4_12
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f113,f109,f103,f117])).

fof(f109,plain,
    ( spl4_11
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f113,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f111,f105])).

fof(f111,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f112,plain,
    ( spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f64,f43,f109])).

fof(f43,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f64,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f45,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f107,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f73,f43,f103])).

fof(f73,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f45,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f101,plain,
    ( ~ spl4_3
    | spl4_9
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f99,f79,f93,f49])).

fof(f49,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f93,plain,
    ( spl4_9
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f99,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_7 ),
    inference(superposition,[],[f34,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f96,plain,
    ( ~ spl4_2
    | ~ spl4_9
    | spl4_1 ),
    inference(avatar_split_clause,[],[f86,f38,f93,f43])).

fof(f38,plain,
    ( spl4_1
  <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f86,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(superposition,[],[f40,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f40,plain,
    ( k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f84,plain,
    ( spl4_7
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f83,f58,f43,f79])).

fof(f58,plain,
    ( spl4_5
  <=> k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f83,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f74,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f74,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f31,f45])).

fof(f61,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f53,f58,f55])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)
      | ~ m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK3(X0,k2_relset_1(sK0,sK1,sK2)),sK1) ) ),
    inference(resolution,[],[f29,f27])).

fof(f27,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k1_relset_1(X0,X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
            & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f47,f43,f49])).

fof(f47,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f36,f45,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f43])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f38])).

fof(f26,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (19177)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.47  % (19177)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (19185)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f41,f46,f52,f61,f84,f96,f101,f107,f112,f120,f144])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl4_7 | ~spl4_12 | ~spl4_4 | ~spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f142,f103,f55,f117,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl4_7 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl4_12 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl4_4 <=> ! [X0] : (~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK3(X0,k2_relset_1(sK0,sK1,sK2)),sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl4_10 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k2_relat_1(sK2) | (~spl4_4 | ~spl4_10)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl4_4 | ~spl4_10)),
% 0.21/0.48    inference(resolution,[],[f121,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1) | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0))) ) | (~spl4_4 | ~spl4_10)),
% 0.21/0.48    inference(forward_demodulation,[],[f114,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3(X0,k2_relat_1(sK2)),sK1) | ~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0))) ) | (~spl4_4 | ~spl4_10)),
% 0.21/0.48    inference(backward_demodulation,[],[f56,f105])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK3(X0,k2_relset_1(sK0,sK1,sK2)),sK1)) ) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl4_12 | ~spl4_10 | ~spl4_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f113,f109,f103,f117])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl4_11 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl4_10 | ~spl4_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f111,f105])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f109])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl4_11 | ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f64,f43,f109])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl4_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f45,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl4_10 | ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f73,f43,f103])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl4_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f45,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ~spl4_3 | spl4_9 | ~spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f99,f79,f93,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl4_3 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl4_9 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl4_7),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl4_7),
% 0.21/0.48    inference(superposition,[],[f34,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ~spl4_2 | ~spl4_9 | spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f86,f38,f93,f43])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl4_1 <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 0.21/0.48    inference(superposition,[],[f40,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f38])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl4_7 | ~spl4_2 | ~spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f83,f58,f43,f79])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl4_5 <=> k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(sK2) | (~spl4_2 | ~spl4_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f74,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f58])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f31,f45])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl4_4 | spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f53,f58,f55])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK3(X0,k2_relset_1(sK0,sK1,sK2)),sK1)) )),
% 0.21/0.48    inference(resolution,[],[f29,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl4_3 | ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f43,f49])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl4_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f36,f45,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f43])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f38])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (19177)------------------------------
% 0.21/0.48  % (19177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19177)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (19177)Memory used [KB]: 10746
% 0.21/0.48  % (19177)Time elapsed: 0.066 s
% 0.21/0.48  % (19177)------------------------------
% 0.21/0.48  % (19177)------------------------------
% 0.21/0.49  % (19170)Success in time 0.127 s
%------------------------------------------------------------------------------
