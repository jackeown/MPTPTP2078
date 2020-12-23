%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t60_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:19 EDT 2019

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 110 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   16
%              Number of atoms          :  141 ( 357 expanded)
%              Number of equality atoms :   33 ( 113 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f89,f172,f186])).

fof(f186,plain,
    ( ~ spl5_0
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f184,f78])).

fof(f78,plain,
    ( m1_setfam_1(sK1,sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_0
  <=> m1_setfam_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f184,plain,
    ( ~ m1_setfam_1(sK1,sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f183,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t60_setfam_1.p',d12_setfam_1)).

fof(f183,plain,
    ( ~ r1_tarski(sK0,k3_tarski(sK1))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f182,f173])).

fof(f173,plain,
    ( k3_tarski(sK1) != sK0
    | ~ spl5_3 ),
    inference(superposition,[],[f87,f90])).

fof(f90,plain,(
    k5_setfam_1(sK0,sK1) = k3_tarski(sK1) ),
    inference(resolution,[],[f49,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t60_setfam_1.p',redefinition_k5_setfam_1)).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k5_setfam_1(sK0,sK1) != sK0
      | ~ m1_setfam_1(sK1,sK0) )
    & ( k5_setfam_1(sK0,sK1) = sK0
      | m1_setfam_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( k5_setfam_1(X0,X1) != X0
          | ~ m1_setfam_1(X1,X0) )
        & ( k5_setfam_1(X0,X1) = X0
          | m1_setfam_1(X1,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( k5_setfam_1(sK0,sK1) != sK0
        | ~ m1_setfam_1(sK1,sK0) )
      & ( k5_setfam_1(sK0,sK1) = sK0
        | m1_setfam_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <~> k5_setfam_1(X0,X1) = X0 )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( m1_setfam_1(X1,X0)
        <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t60_setfam_1.p',t60_setfam_1)).

fof(f87,plain,
    ( k5_setfam_1(sK0,sK1) != sK0
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_3
  <=> k5_setfam_1(sK0,sK1) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f182,plain,
    ( k3_tarski(sK1) = sK0
    | ~ r1_tarski(sK0,k3_tarski(sK1)) ),
    inference(resolution,[],[f177,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/setfam_1__t60_setfam_1.p',d10_xboole_0)).

fof(f177,plain,(
    r1_tarski(k3_tarski(sK1),sK0) ),
    inference(resolution,[],[f175,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t60_setfam_1.p',t3_subset)).

fof(f175,plain,(
    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f174,f49])).

fof(f174,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f60,f90])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t60_setfam_1.p',dt_k5_setfam_1)).

fof(f172,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f168,f81])).

fof(f81,plain,
    ( ~ m1_setfam_1(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_1
  <=> ~ m1_setfam_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f168,plain,
    ( m1_setfam_1(sK1,sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f166,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f166,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | m1_setfam_1(sK1,X1) )
    | ~ spl5_2 ),
    inference(superposition,[],[f65,f164])).

fof(f164,plain,
    ( k3_tarski(sK1) = sK0
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f90,f84])).

fof(f84,plain,
    ( k5_setfam_1(sK0,sK1) = sK0
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_2
  <=> k5_setfam_1(sK0,sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      | m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,
    ( spl5_0
    | spl5_2 ),
    inference(avatar_split_clause,[],[f50,f83,f77])).

fof(f50,plain,
    ( k5_setfam_1(sK0,sK1) = sK0
    | m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f51,f86,f80])).

fof(f51,plain,
    ( k5_setfam_1(sK0,sK1) != sK0
    | ~ m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
