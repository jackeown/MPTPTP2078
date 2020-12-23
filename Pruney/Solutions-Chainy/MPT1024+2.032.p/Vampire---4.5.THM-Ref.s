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
% DateTime   : Thu Dec  3 13:06:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 160 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  295 ( 773 expanded)
%              Number of equality atoms :   23 (  87 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f82,f177,f289,f299])).

fof(f299,plain,
    ( ~ spl7_6
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl7_6
    | spl7_7 ),
    inference(unit_resulting_resolution,[],[f30,f181,f171,f120])).

fof(f120,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | r2_hidden(k4_tarski(sK5(X0,X2,X1),X0),X1)
      | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f35,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f171,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl7_6
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f181,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),X0),sK3)
    | spl7_7 ),
    inference(resolution,[],[f176,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(k4_tarski(X0,X1),sK3) ) ),
    inference(resolution,[],[f91,f30])).

fof(f91,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X7)))
      | ~ r2_hidden(k4_tarski(X3,X5),X6)
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f176,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_7
  <=> r2_hidden(sK5(sK4,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ r2_hidden(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f289,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f287,f30])).

fof(f287,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl7_6 ),
    inference(subsumption_resolution,[],[f282,f172])).

fof(f172,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f170])).

fof(f282,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f265,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ6_eqProxy(k7_relset_1(X0,X1,X2,X3),k9_relat_1(X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_proxy_replacement,[],[f42,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f265,plain,(
    ! [X30] :
      ( ~ sQ6_eqProxy(k7_relset_1(sK0,sK1,sK3,sK2),X30)
      | r2_hidden(sK4,X30) ) ),
    inference(resolution,[],[f211,f31])).

fof(f31,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ sQ6_eqProxy(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f59,f64])).

fof(f64,plain,(
    ! [X0] : sQ6_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f47])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sQ6_eqProxy(X0,X1)
      | ~ sQ6_eqProxy(X2,X3)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f47])).

fof(f177,plain,
    ( ~ spl7_6
    | ~ spl7_7
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f168,f76,f72,f174,f170])).

fof(f72,plain,
    ( spl7_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f76,plain,
    ( spl7_2
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f168,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f167,f73])).

fof(f73,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f167,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( ~ r2_hidden(sK5(sK4,sK2,sK3),sK0)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f130,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK5(sK4,X0,sK3),sK0)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0)) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f122,f77])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f122,plain,
    ( ! [X10,X9] :
        ( r2_hidden(k4_tarski(sK5(X9,X10,sK3),X9),sK3)
        | ~ r2_hidden(X9,k9_relat_1(sK3,X10)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f35,f73])).

fof(f82,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f30,f74,f38])).

fof(f74,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f78,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f70,f76,f72])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f69,f29])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f49,f48])).

fof(f48,plain,(
    ! [X5] :
      ( ~ sQ6_eqProxy(k1_funct_1(sK3,X5),sK4)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(equality_proxy_replacement,[],[f32,f47])).

fof(f32,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_proxy_replacement,[],[f40,f47])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:03:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (14856)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (14856)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f78,f82,f177,f289,f299])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    ~spl7_6 | spl7_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f293])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    $false | (~spl7_6 | spl7_7)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f30,f181,f171,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | r2_hidden(k4_tarski(sK5(X0,X2,X1),X0),X1) | ~r2_hidden(X0,k9_relat_1(X1,X2))) )),
% 0.21/0.49    inference(resolution,[],[f35,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(rectify,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl7_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f170])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl7_6 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(sK4,sK2,sK3),X0),sK3)) ) | spl7_7),
% 0.21/0.49    inference(resolution,[],[f176,f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK3)) )),
% 0.21/0.49    inference(resolution,[],[f91,f30])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X6,X4,X7,X5,X3] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X7))) | ~r2_hidden(k4_tarski(X3,X5),X6) | r2_hidden(X3,X4)) )),
% 0.21/0.49    inference(resolution,[],[f43,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | spl7_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    spl7_7 <=> r2_hidden(sK5(sK4,sK2,sK3),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f19,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    spl7_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f288])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    $false | spl7_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f287,f30])).
% 0.21/0.49  fof(f287,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl7_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f282,f172])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | spl7_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f170])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(resolution,[],[f265,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (sQ6_eqProxy(k7_relset_1(X0,X1,X2,X3),k9_relat_1(X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f42,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.49    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ( ! [X30] : (~sQ6_eqProxy(k7_relset_1(sK0,sK1,sK3,sK2),X30) | r2_hidden(sK4,X30)) )),
% 0.21/0.49    inference(resolution,[],[f211,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~sQ6_eqProxy(X0,X1) | r2_hidden(X2,X1)) )),
% 0.21/0.49    inference(resolution,[],[f59,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0] : (sQ6_eqProxy(X0,X0)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f47])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~sQ6_eqProxy(X0,X1) | ~sQ6_eqProxy(X2,X3) | ~r2_hidden(X0,X2) | r2_hidden(X1,X3)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f47])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ~spl7_6 | ~spl7_7 | ~spl7_1 | ~spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f168,f76,f72,f174,f170])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl7_1 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl7_2 <=> ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl7_1 | ~spl7_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f167,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl7_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~v1_relat_1(sK3) | (~spl7_1 | ~spl7_2)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f165])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK4,sK2,sK3),sK0) | ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~v1_relat_1(sK3) | (~spl7_1 | ~spl7_2)),
% 0.21/0.49    inference(resolution,[],[f130,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK5(sK4,X0,sK3),sK2) | ~r2_hidden(sK5(sK4,X0,sK3),sK0) | ~r2_hidden(sK4,k9_relat_1(sK3,X0))) ) | (~spl7_1 | ~spl7_2)),
% 0.21/0.49    inference(resolution,[],[f122,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK2)) ) | ~spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X10,X9] : (r2_hidden(k4_tarski(sK5(X9,X10,sK3),X9),sK3) | ~r2_hidden(X9,k9_relat_1(sK3,X10))) ) | ~spl7_1),
% 0.21/0.49    inference(resolution,[],[f35,f73])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl7_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    $false | spl7_1),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f30,f74,f38])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | spl7_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~spl7_1 | spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f70,f76,f72])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~v1_relat_1(sK3) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f69,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f49,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X5] : (~sQ6_eqProxy(k1_funct_1(sK3,X5),sK4) | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f32,f47])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sQ6_eqProxy(k1_funct_1(X2,X0),X1) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f40,f47])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (14856)------------------------------
% 0.21/0.49  % (14856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14856)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (14856)Memory used [KB]: 6268
% 0.21/0.49  % (14856)Time elapsed: 0.067 s
% 0.21/0.49  % (14856)------------------------------
% 0.21/0.49  % (14856)------------------------------
% 0.21/0.50  % (14850)Success in time 0.132 s
%------------------------------------------------------------------------------
