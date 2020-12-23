%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 301 expanded)
%              Number of leaves         :   21 ( 104 expanded)
%              Depth                    :   21
%              Number of atoms          :  321 (1272 expanded)
%              Number of equality atoms :   41 ( 221 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f70,f88,f170,f179,f187])).

fof(f187,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f185,f65])).

fof(f65,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl9_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f185,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f184,f180])).

fof(f180,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f72,f59])).

fof(f59,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl9_2
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f72,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f35,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        & r2_hidden(sK3,sK1) ) )
    & ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ! [X5] :
          ( r2_hidden(k4_tarski(sK4(X5),X5),sK2)
          | ~ r2_hidden(X5,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),sK2)
            & r2_hidden(X3,sK1) ) )
      & ( sK1 = k2_relset_1(sK0,sK1,sK2)
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),sK2)
            | ~ r2_hidden(X5,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),sK2)
        & r2_hidden(X3,sK1) )
   => ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X6,X5),sK2)
     => r2_hidden(k4_tarski(sK4(X5),X5),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(f184,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f56,f53])).

fof(f53,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f56,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl9_1
  <=> ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f179,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f177,f87])).

fof(f87,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(sK2,sK1)),sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl9_6
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(sK2,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f177,plain,
    ( r2_hidden(k4_tarski(sK4(sK6(sK2,sK1)),sK6(sK2,sK1)),sK2)
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f83,f69])).

fof(f69,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | r2_hidden(k4_tarski(sK4(X5),X5),sK2) )
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl9_4
  <=> ! [X5] :
        ( r2_hidden(k4_tarski(sK4(X5),X5),sK2)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f83,plain,
    ( r2_hidden(sK6(sK2,sK1),sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl9_5
  <=> r2_hidden(sK6(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f170,plain,
    ( spl9_2
    | spl9_5 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl9_2
    | spl9_5 ),
    inference(subsumption_resolution,[],[f166,f138])).

fof(f138,plain,
    ( ! [X0] : ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1))
    | spl9_2
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f120,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f120,plain,
    ( ! [X0] : ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | spl9_2
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f107,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f107,plain,
    ( ~ v5_relat_1(k2_zfmisc_1(sK0,sK1),sK1)
    | spl9_2
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f39,f84,f100,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(f100,plain,
    ( r2_hidden(sK6(sK2,sK1),k2_relat_1(k2_zfmisc_1(sK0,sK1)))
    | spl9_2
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f94,f52])).

fof(f52,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,
    ( r2_hidden(k4_tarski(sK7(sK2,sK1),sK6(sK2,sK1)),k2_zfmisc_1(sK0,sK1))
    | spl9_2
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f73,f90,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f90,plain,
    ( r2_hidden(k4_tarski(sK7(sK2,sK1),sK6(sK2,sK1)),sK2)
    | spl9_2
    | spl9_5 ),
    inference(subsumption_resolution,[],[f89,f84])).

fof(f89,plain,
    ( r2_hidden(k4_tarski(sK7(sK2,sK1),sK6(sK2,sK1)),sK2)
    | r2_hidden(sK6(sK2,sK1),sK1)
    | spl9_2 ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,
    ( ! [X0] :
        ( sK1 != X0
        | r2_hidden(k4_tarski(sK7(sK2,X0),sK6(sK2,X0)),sK2)
        | r2_hidden(sK6(sK2,X0),X0) )
    | spl9_2 ),
    inference(superposition,[],[f75,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl9_2 ),
    inference(subsumption_resolution,[],[f74,f35])).

fof(f74,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl9_2 ),
    inference(superposition,[],[f60,f50])).

fof(f60,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f73,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f35,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,
    ( ~ r2_hidden(sK6(sK2,sK1),sK1)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f166,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | spl9_2
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f151,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f151,plain,
    ( ! [X0] : r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1)),k2_zfmisc_1(sK0,sK1))
    | spl9_2
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f138,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,
    ( ~ spl9_5
    | spl9_6
    | spl9_2 ),
    inference(avatar_split_clause,[],[f80,f58,f86,f82])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6(sK2,sK1)),sK2)
        | ~ r2_hidden(sK6(sK2,sK1),sK1) )
    | spl9_2 ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,
    ( ! [X2,X1] :
        ( sK1 != X1
        | ~ r2_hidden(k4_tarski(X2,sK6(sK2,X1)),sK2)
        | ~ r2_hidden(sK6(sK2,X1),X1) )
    | spl9_2 ),
    inference(superposition,[],[f75,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,
    ( spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f36,f58,f68])).

fof(f36,plain,(
    ! [X5] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | r2_hidden(k4_tarski(sK4(X5),X5),sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f37,f58,f63])).

fof(f37,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f38,f58,f55])).

fof(f38,plain,(
    ! [X4] :
      ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:22:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (1217)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % (1231)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.49  % (1215)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (1224)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.50  % (1217)Refutation not found, incomplete strategy% (1217)------------------------------
% 0.22/0.50  % (1217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1217)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (1217)Memory used [KB]: 10618
% 0.22/0.50  % (1217)Time elapsed: 0.096 s
% 0.22/0.50  % (1217)------------------------------
% 0.22/0.50  % (1217)------------------------------
% 0.22/0.50  % (1224)Refutation not found, incomplete strategy% (1224)------------------------------
% 0.22/0.50  % (1224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1224)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (1224)Memory used [KB]: 10618
% 0.22/0.50  % (1224)Time elapsed: 0.097 s
% 0.22/0.50  % (1224)------------------------------
% 0.22/0.50  % (1224)------------------------------
% 0.22/0.51  % (1211)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (1209)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (1211)Refutation not found, incomplete strategy% (1211)------------------------------
% 0.22/0.52  % (1211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1211)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1211)Memory used [KB]: 6140
% 0.22/0.52  % (1211)Time elapsed: 0.095 s
% 0.22/0.52  % (1211)------------------------------
% 0.22/0.52  % (1211)------------------------------
% 0.22/0.52  % (1227)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (1227)Refutation not found, incomplete strategy% (1227)------------------------------
% 0.22/0.52  % (1227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1227)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1227)Memory used [KB]: 10746
% 0.22/0.52  % (1227)Time elapsed: 0.108 s
% 0.22/0.52  % (1227)------------------------------
% 0.22/0.52  % (1227)------------------------------
% 0.22/0.52  % (1214)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (1233)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (1208)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (1212)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (1235)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (1234)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (1228)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (1210)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (1222)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (1226)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (1219)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (1230)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (1225)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (1207)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (1221)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (1218)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (1233)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f188,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f61,f66,f70,f88,f170,f179,f187])).
% 0.22/0.56  fof(f187,plain,(
% 0.22/0.56    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f186])).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    $false | (~spl9_1 | ~spl9_2 | ~spl9_3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f185,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    r2_hidden(sK3,sK1) | ~spl9_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    spl9_3 <=> r2_hidden(sK3,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.56  fof(f185,plain,(
% 0.22/0.56    ~r2_hidden(sK3,sK1) | (~spl9_1 | ~spl9_2)),
% 0.22/0.56    inference(forward_demodulation,[],[f184,f180])).
% 0.22/0.56  fof(f180,plain,(
% 0.22/0.56    sK1 = k2_relat_1(sK2) | ~spl9_2),
% 0.22/0.56    inference(backward_demodulation,[],[f72,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl9_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    spl9_2 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f35,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    (sK1 != k2_relset_1(sK0,sK1,sK2) | (! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2) & r2_hidden(sK3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X5] : (r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f22,f21,f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),sK2) & r2_hidden(X3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),sK2) & r2_hidden(X3,sK1)) => (! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2) & r2_hidden(sK3,sK1))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),sK2) => r2_hidden(k4_tarski(sK4(X5),X5),sK2))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(rectify,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.56    inference(negated_conjecture,[],[f8])).
% 0.22/0.56  fof(f8,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~spl9_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f56,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.22/0.56    inference(equality_resolution,[],[f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.56    inference(rectify,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2)) ) | ~spl9_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    spl9_1 <=> ! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    ~spl9_4 | ~spl9_5 | ~spl9_6),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f178])).
% 0.22/0.56  fof(f178,plain,(
% 0.22/0.56    $false | (~spl9_4 | ~spl9_5 | ~spl9_6)),
% 0.22/0.56    inference(subsumption_resolution,[],[f177,f87])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6(sK2,sK1)),sK2)) ) | ~spl9_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f86])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    spl9_6 <=> ! [X0] : ~r2_hidden(k4_tarski(X0,sK6(sK2,sK1)),sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.56  fof(f177,plain,(
% 0.22/0.56    r2_hidden(k4_tarski(sK4(sK6(sK2,sK1)),sK6(sK2,sK1)),sK2) | (~spl9_4 | ~spl9_5)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f83,f69])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(k4_tarski(sK4(X5),X5),sK2)) ) | ~spl9_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    spl9_4 <=> ! [X5] : (r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    r2_hidden(sK6(sK2,sK1),sK1) | ~spl9_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f82])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    spl9_5 <=> r2_hidden(sK6(sK2,sK1),sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.56  fof(f170,plain,(
% 0.22/0.56    spl9_2 | spl9_5),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f169])).
% 0.22/0.56  fof(f169,plain,(
% 0.22/0.56    $false | (spl9_2 | spl9_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f166,f138])).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1))) ) | (spl9_2 | spl9_5)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f120,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (spl9_2 | spl9_5)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f107,f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ~v5_relat_1(k2_zfmisc_1(sK0,sK1),sK1) | (spl9_2 | spl9_5)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f39,f84,f100,f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    r2_hidden(sK6(sK2,sK1),k2_relat_1(k2_zfmisc_1(sK0,sK1))) | (spl9_2 | spl9_5)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f94,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    r2_hidden(k4_tarski(sK7(sK2,sK1),sK6(sK2,sK1)),k2_zfmisc_1(sK0,sK1)) | (spl9_2 | spl9_5)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f73,f90,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(rectify,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    r2_hidden(k4_tarski(sK7(sK2,sK1),sK6(sK2,sK1)),sK2) | (spl9_2 | spl9_5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f89,f84])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    r2_hidden(k4_tarski(sK7(sK2,sK1),sK6(sK2,sK1)),sK2) | r2_hidden(sK6(sK2,sK1),sK1) | spl9_2),
% 0.22/0.56    inference(equality_resolution,[],[f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X0] : (sK1 != X0 | r2_hidden(k4_tarski(sK7(sK2,X0),sK6(sK2,X0)),sK2) | r2_hidden(sK6(sK2,X0),X0)) ) | spl9_2),
% 0.22/0.56    inference(superposition,[],[f75,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    sK1 != k2_relat_1(sK2) | spl9_2),
% 0.22/0.56    inference(subsumption_resolution,[],[f74,f35])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl9_2),
% 0.22/0.56    inference(superposition,[],[f60,f50])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    sK1 != k2_relset_1(sK0,sK1,sK2) | spl9_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f58])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f35,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ~r2_hidden(sK6(sK2,sK1),sK1) | spl9_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f82])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.56  fof(f166,plain,(
% 0.22/0.56    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | (spl9_2 | spl9_5)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f151,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f151,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1)),k2_zfmisc_1(sK0,sK1))) ) | (spl9_2 | spl9_5)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f138,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    ~spl9_5 | spl9_6 | spl9_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f80,f58,f86,f82])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6(sK2,sK1)),sK2) | ~r2_hidden(sK6(sK2,sK1),sK1)) ) | spl9_2),
% 0.22/0.56    inference(equality_resolution,[],[f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X2,X1] : (sK1 != X1 | ~r2_hidden(k4_tarski(X2,sK6(sK2,X1)),sK2) | ~r2_hidden(sK6(sK2,X1),X1)) ) | spl9_2),
% 0.22/0.56    inference(superposition,[],[f75,f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    spl9_4 | spl9_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f36,f58,f68])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X5] : (sK1 = k2_relset_1(sK0,sK1,sK2) | r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    spl9_3 | ~spl9_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f37,f58,f63])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    spl9_1 | ~spl9_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f38,f58,f55])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X4] : (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (1233)------------------------------
% 0.22/0.56  % (1233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1233)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (1233)Memory used [KB]: 10874
% 0.22/0.56  % (1233)Time elapsed: 0.130 s
% 0.22/0.56  % (1233)------------------------------
% 0.22/0.56  % (1233)------------------------------
% 0.22/0.56  % (1206)Success in time 0.194 s
%------------------------------------------------------------------------------
