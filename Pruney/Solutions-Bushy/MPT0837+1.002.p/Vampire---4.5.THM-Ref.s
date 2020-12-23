%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0837+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:44 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 240 expanded)
%              Number of leaves         :   27 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  362 (1319 expanded)
%              Number of equality atoms :   12 (  33 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f715,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f102,f139,f443,f444,f470,f479,f482,f714])).

fof(f714,plain,
    ( ~ spl9_1
    | ~ spl9_8
    | spl9_15 ),
    inference(avatar_contradiction_clause,[],[f713])).

fof(f713,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_8
    | spl9_15 ),
    inference(subsumption_resolution,[],[f711,f480])).

fof(f480,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f105,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ! [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
          | ~ m1_subset_1(X4,sK1) )
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & ( ( r2_hidden(k4_tarski(sK4,sK3),sK2)
        & m1_subset_1(sK4,sK1) )
      | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f25,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                          | ~ m1_subset_1(X4,X1) )
                      | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                    & ( ? [X5] :
                          ( r2_hidden(k4_tarski(X5,X3),X2)
                          & m1_subset_1(X5,X1) )
                      | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,sK0,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,sK0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                      | ~ m1_subset_1(X4,X1) )
                  | ~ r2_hidden(X3,k2_relset_1(X1,sK0,X2)) )
                & ( ? [X5] :
                      ( r2_hidden(k4_tarski(X5,X3),X2)
                      & m1_subset_1(X5,X1) )
                  | r2_hidden(X3,k2_relset_1(X1,sK0,X2)) ) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                    | ~ m1_subset_1(X4,sK1) )
                | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) )
              & ( ? [X5] :
                    ( r2_hidden(k4_tarski(X5,X3),X2)
                    & m1_subset_1(X5,sK1) )
                | r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                  | ~ m1_subset_1(X4,sK1) )
              | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) )
            & ( ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X3),X2)
                  & m1_subset_1(X5,sK1) )
              | r2_hidden(X3,k2_relset_1(sK1,sK0,X2)) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X3),sK2)
                | ~ m1_subset_1(X4,sK1) )
            | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) )
          & ( ? [X5] :
                ( r2_hidden(k4_tarski(X5,X3),sK2)
                & m1_subset_1(X5,sK1) )
            | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X3),sK2)
              | ~ m1_subset_1(X4,sK1) )
          | ~ r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) )
        & ( ? [X5] :
              ( r2_hidden(k4_tarski(X5,X3),sK2)
              & m1_subset_1(X5,sK1) )
          | r2_hidden(X3,k2_relset_1(sK1,sK0,sK2)) ) )
   => ( ( ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
            | ~ m1_subset_1(X4,sK1) )
        | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,sK3),sK2)
            & m1_subset_1(X5,sK1) )
        | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X5] :
        ( r2_hidden(k4_tarski(X5,sK3),sK2)
        & m1_subset_1(X5,sK1) )
   => ( r2_hidden(k4_tarski(sK4,sK3),sK2)
      & m1_subset_1(sK4,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X3),X2)
                        & m1_subset_1(X5,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( ~ r2_hidden(k4_tarski(X4,X3),X2)
                        | ~ m1_subset_1(X4,X1) )
                    | ~ r2_hidden(X3,k2_relset_1(X1,X0,X2)) )
                  & ( ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) )
                    | r2_hidden(X3,k2_relset_1(X1,X0,X2)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <~> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ! [X3] :
                    ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X4,X3),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

% (7425)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (7426)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ! [X3] :
                  ( r2_hidden(X3,k2_relset_1(X1,X0,X2))
                <=> ? [X4] :
                      ( r2_hidden(k4_tarski(X4,X3),X2)
                      & m1_subset_1(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

fof(f105,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl9_1 ),
    inference(superposition,[],[f65,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f65,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl9_1
  <=> r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f711,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_8
    | spl9_15 ),
    inference(resolution,[],[f689,f478])).

fof(f478,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3),sK1)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl9_15
  <=> m1_subset_1(sK8(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f689,plain,
    ( ! [X0] :
        ( m1_subset_1(sK8(sK2,X0),sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl9_8 ),
    inference(resolution,[],[f682,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f682,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK2,X0),sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl9_8 ),
    inference(resolution,[],[f499,f57])).

fof(f57,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f30,f33,f32,f31])).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f499,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | r2_hidden(X2,sK1) )
    | ~ spl9_8 ),
    inference(resolution,[],[f138,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f138,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK1,sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl9_8
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k2_zfmisc_1(sK1,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f482,plain,
    ( ~ spl9_1
    | spl9_14 ),
    inference(avatar_contradiction_clause,[],[f481])).

fof(f481,plain,
    ( $false
    | ~ spl9_1
    | spl9_14 ),
    inference(subsumption_resolution,[],[f475,f480])).

fof(f475,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | spl9_14 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl9_14
  <=> r2_hidden(sK3,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f479,plain,
    ( ~ spl9_14
    | ~ spl9_15
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f107,f62,f477,f474])).

fof(f62,plain,
    ( spl9_2
  <=> ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f107,plain,
    ( ~ m1_subset_1(sK8(sK2,sK3),sK1)
    | ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_2 ),
    inference(resolution,[],[f63,f57])).

fof(f63,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f470,plain,(
    ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f460,f38])).

fof(f38,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f460,plain,
    ( v1_xboole_0(sK1)
    | ~ spl9_10 ),
    inference(resolution,[],[f162,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f45,f43])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f2,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f162,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl9_10
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f444,plain,
    ( spl9_9
    | spl9_10
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f415,f134,f161,f158])).

fof(f158,plain,
    ( spl9_9
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f134,plain,
    ( spl9_7
  <=> v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f415,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl9_7 ),
    inference(resolution,[],[f135,f115])).

fof(f115,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X19,X17))
      | ~ r2_hidden(X18,X19)
      | ~ r2_hidden(X16,X17) ) ),
    inference(resolution,[],[f55,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f135,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK0))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f443,plain,(
    ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f434,f37])).

fof(f37,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f434,plain,
    ( v1_xboole_0(sK0)
    | ~ spl9_9 ),
    inference(resolution,[],[f159,f78])).

fof(f159,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f158])).

fof(f139,plain,
    ( spl9_7
    | spl9_8 ),
    inference(avatar_split_clause,[],[f132,f137,f134])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | v1_xboole_0(k2_zfmisc_1(sK1,sK0))
      | r2_hidden(X0,k2_zfmisc_1(sK1,sK0)) ) ),
    inference(resolution,[],[f88,f45])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k2_zfmisc_1(sK1,sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f102,plain,
    ( spl9_1
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f100,f39])).

fof(f100,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f99,f87])).

fof(f87,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_3 ),
    inference(resolution,[],[f56,f68])).

fof(f68,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl9_3
  <=> r2_hidden(k4_tarski(sK4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f56,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f99,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl9_1 ),
    inference(superposition,[],[f60,f51])).

fof(f60,plain,
    ( ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f69,plain,
    ( spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f41,f67,f59])).

fof(f41,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),sK2)
    | r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f42,f62,f59])).

fof(f42,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      | ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(sK3,k2_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
