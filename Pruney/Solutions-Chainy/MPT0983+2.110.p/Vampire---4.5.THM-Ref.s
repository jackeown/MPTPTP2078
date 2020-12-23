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
% DateTime   : Thu Dec  3 13:01:50 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 540 expanded)
%              Number of leaves         :   47 ( 179 expanded)
%              Depth                    :   18
%              Number of atoms          :  673 (2327 expanded)
%              Number of equality atoms :   61 ( 143 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f963,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f380,f382,f463,f494,f501,f503,f505,f545,f560,f568,f571,f583,f602,f741,f766,f774,f776,f789,f816,f831,f962])).

fof(f962,plain,
    ( spl6_1
    | ~ spl6_54 ),
    inference(avatar_contradiction_clause,[],[f960])).

fof(f960,plain,
    ( $false
    | spl6_1
    | ~ spl6_54 ),
    inference(resolution,[],[f896,f243])).

fof(f243,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f104,f178])).

fof(f178,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f170,f150])).

fof(f150,plain,(
    ! [X0] : r1_tarski(k6_partfun1(k1_xboole_0),X0) ),
    inference(resolution,[],[f148,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f148,plain,(
    ! [X2] : ~ r2_hidden(X2,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f145,f80])).

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
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

fof(f145,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f131,f74])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f126,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f126,plain,(
    ! [X1] : v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f124,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f124,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f123,f109])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f123,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f83,f69])).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f170,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f91,f129])).

fof(f129,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f127,f93])).

fof(f127,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(resolution,[],[f124,f80])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f104,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f72,f70])).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f72,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f896,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl6_1
    | ~ spl6_54 ),
    inference(backward_demodulation,[],[f117,f891])).

fof(f891,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_54 ),
    inference(resolution,[],[f890,f170])).

fof(f890,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl6_54 ),
    inference(resolution,[],[f888,f93])).

fof(f888,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl6_54 ),
    inference(resolution,[],[f880,f80])).

fof(f880,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_54 ),
    inference(resolution,[],[f854,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f124,f77])).

fof(f854,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_54 ),
    inference(forward_demodulation,[],[f833,f179])).

fof(f179,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f170,f135])).

fof(f135,plain,(
    ! [X2,X1] : r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(resolution,[],[f133,f93])).

fof(f133,plain,(
    ! [X4,X5] : ~ r2_hidden(X4,k2_zfmisc_1(k1_xboole_0,X5)) ),
    inference(resolution,[],[f126,f80])).

fof(f833,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_54 ),
    inference(backward_demodulation,[],[f63,f811])).

fof(f811,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f809])).

fof(f809,plain,
    ( spl6_54
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f46,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f117,plain,
    ( ~ v2_funct_1(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f831,plain,(
    spl6_55 ),
    inference(avatar_contradiction_clause,[],[f829])).

fof(f829,plain,
    ( $false
    | spl6_55 ),
    inference(resolution,[],[f815,f104])).

fof(f815,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl6_55 ),
    inference(avatar_component_clause,[],[f813])).

fof(f813,plain,
    ( spl6_55
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f816,plain,
    ( spl6_54
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_55
    | ~ spl6_14
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f807,f787,f377,f813,f491,f487,f809])).

fof(f487,plain,
    ( spl6_23
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f491,plain,
    ( spl6_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f377,plain,
    ( spl6_14
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f787,plain,
    ( spl6_53
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f807,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ spl6_14
    | ~ spl6_53 ),
    inference(forward_demodulation,[],[f806,f379])).

fof(f379,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f377])).

fof(f806,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ spl6_53 ),
    inference(resolution,[],[f788,f65])).

fof(f65,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f788,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,sK1,X0)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0 )
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f787])).

fof(f789,plain,
    ( ~ spl6_22
    | spl6_53
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f785,f566,f787,f483])).

fof(f483,plain,
    ( spl6_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f566,plain,
    ( spl6_33
  <=> ! [X1,X3,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK2,X1,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f785,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) )
    | ~ spl6_33 ),
    inference(resolution,[],[f567,f62])).

fof(f62,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f567,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK2,X1,X2)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f566])).

fof(f776,plain,(
    spl6_52 ),
    inference(avatar_contradiction_clause,[],[f775])).

fof(f775,plain,
    ( $false
    | spl6_52 ),
    inference(resolution,[],[f773,f109])).

fof(f773,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl6_52 ),
    inference(avatar_component_clause,[],[f771])).

fof(f771,plain,
    ( spl6_52
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f774,plain,
    ( ~ spl6_31
    | ~ spl6_52
    | ~ spl6_35
    | spl6_51 ),
    inference(avatar_split_clause,[],[f769,f763,f599,f771,f553])).

fof(f553,plain,
    ( spl6_31
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f599,plain,
    ( spl6_35
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f763,plain,
    ( spl6_51
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f769,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_35
    | spl6_51 ),
    inference(forward_demodulation,[],[f768,f601])).

fof(f601,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f599])).

fof(f768,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | spl6_51 ),
    inference(resolution,[],[f765,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f765,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl6_51 ),
    inference(avatar_component_clause,[],[f763])).

fof(f766,plain,
    ( ~ spl6_31
    | ~ spl6_51
    | spl6_2
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f757,f599,f119,f763,f553])).

fof(f119,plain,
    ( spl6_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f757,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_35 ),
    inference(superposition,[],[f108,f601])).

fof(f108,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f741,plain,
    ( ~ spl6_31
    | spl6_34 ),
    inference(avatar_contradiction_clause,[],[f738])).

fof(f738,plain,
    ( $false
    | ~ spl6_31
    | spl6_34 ),
    inference(resolution,[],[f736,f597])).

fof(f597,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl6_34 ),
    inference(avatar_component_clause,[],[f595])).

fof(f595,plain,
    ( spl6_34
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f736,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_31 ),
    inference(resolution,[],[f585,f66])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f585,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | r1_tarski(k2_relat_1(sK3),X1) )
    | ~ spl6_31 ),
    inference(resolution,[],[f554,f251])).

fof(f251,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f96,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f554,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f553])).

fof(f602,plain,
    ( ~ spl6_34
    | spl6_35
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f593,f557,f599,f595])).

fof(f557,plain,
    ( spl6_32
  <=> r1_tarski(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f593,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_32 ),
    inference(resolution,[],[f559,f91])).

fof(f559,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f557])).

fof(f583,plain,(
    spl6_31 ),
    inference(avatar_contradiction_clause,[],[f581])).

fof(f581,plain,
    ( $false
    | spl6_31 ),
    inference(resolution,[],[f580,f82])).

fof(f82,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f580,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl6_31 ),
    inference(resolution,[],[f562,f66])).

fof(f562,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_31 ),
    inference(resolution,[],[f555,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f555,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f553])).

fof(f571,plain,(
    spl6_30 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | spl6_30 ),
    inference(resolution,[],[f563,f82])).

fof(f563,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl6_30 ),
    inference(resolution,[],[f561,f63])).

fof(f561,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_30 ),
    inference(resolution,[],[f551,f79])).

fof(f551,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f549])).

fof(f549,plain,
    ( spl6_30
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f568,plain,
    ( ~ spl6_17
    | spl6_33
    | spl6_1 ),
    inference(avatar_split_clause,[],[f564,f115,f566,f452])).

fof(f452,plain,
    ( spl6_17
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f564,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_xboole_0 = X0
        | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(X3,X2,X0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(sK2,X1,X2)
        | ~ v1_funct_1(sK2) )
    | spl6_1 ),
    inference(resolution,[],[f97,f117])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f560,plain,
    ( ~ spl6_30
    | ~ spl6_31
    | spl6_32
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f547,f533,f557,f553,f549])).

fof(f533,plain,
    ( spl6_27
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f547,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f546,f106])).

fof(f106,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f76,f70])).

fof(f76,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f546,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl6_27 ),
    inference(superposition,[],[f78,f535])).

fof(f535,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f533])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f545,plain,
    ( ~ spl6_17
    | ~ spl6_22
    | spl6_27
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f529,f377,f533,f483,f452])).

fof(f529,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_14 ),
    inference(superposition,[],[f379,f468])).

fof(f468,plain,(
    ! [X2,X0,X1] :
      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f437,f66])).

fof(f437,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v1_funct_1(X9) ) ),
    inference(resolution,[],[f101,f64])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f505,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | spl6_24 ),
    inference(resolution,[],[f493,f66])).

fof(f493,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f491])).

fof(f503,plain,(
    spl6_22 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | spl6_22 ),
    inference(resolution,[],[f485,f63])).

fof(f485,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f483])).

fof(f501,plain,(
    spl6_23 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | spl6_23 ),
    inference(resolution,[],[f489,f64])).

fof(f489,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f487])).

fof(f494,plain,
    ( ~ spl6_17
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_24
    | spl6_12 ),
    inference(avatar_split_clause,[],[f478,f369,f491,f487,f483,f452])).

fof(f369,plain,
    ( spl6_12
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f478,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl6_12 ),
    inference(resolution,[],[f103,f371])).

fof(f371,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f369])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f463,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | spl6_17 ),
    inference(resolution,[],[f454,f61])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f454,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f452])).

fof(f382,plain,(
    spl6_13 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | spl6_13 ),
    inference(resolution,[],[f375,f74])).

fof(f375,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl6_13
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f380,plain,
    ( ~ spl6_12
    | ~ spl6_13
    | spl6_14 ),
    inference(avatar_split_clause,[],[f365,f377,f373,f369])).

fof(f365,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f99,f67])).

fof(f67,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f122,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f68,f119,f115])).

fof(f68,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:55:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (8414)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (8427)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (8411)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (8416)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (8439)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (8423)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (8413)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (8412)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (8417)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (8424)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (8422)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (8434)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.55  % (8426)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.55  % (8419)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.55  % (8428)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.55  % (8432)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.55  % (8431)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.55  % (8438)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.55  % (8418)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.56  % (8435)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.56  % (8421)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.56  % (8437)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.56  % (8420)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.56  % (8425)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.56  % (8415)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.56  % (8430)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.56  % (8436)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.56  % (8440)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.56  % (8433)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.56/0.57  % (8433)Refutation not found, incomplete strategy% (8433)------------------------------
% 1.56/0.57  % (8433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (8433)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (8433)Memory used [KB]: 10874
% 1.56/0.57  % (8433)Time elapsed: 0.145 s
% 1.56/0.57  % (8433)------------------------------
% 1.56/0.57  % (8433)------------------------------
% 1.56/0.57  % (8428)Refutation not found, incomplete strategy% (8428)------------------------------
% 1.56/0.57  % (8428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (8428)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (8428)Memory used [KB]: 10746
% 1.56/0.57  % (8428)Time elapsed: 0.155 s
% 1.56/0.57  % (8428)------------------------------
% 1.56/0.57  % (8428)------------------------------
% 1.56/0.58  % (8429)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.56/0.60  % (8423)Refutation found. Thanks to Tanya!
% 1.56/0.60  % SZS status Theorem for theBenchmark
% 1.56/0.60  % SZS output start Proof for theBenchmark
% 1.56/0.60  fof(f963,plain,(
% 1.56/0.60    $false),
% 1.56/0.60    inference(avatar_sat_refutation,[],[f122,f380,f382,f463,f494,f501,f503,f505,f545,f560,f568,f571,f583,f602,f741,f766,f774,f776,f789,f816,f831,f962])).
% 1.56/0.60  fof(f962,plain,(
% 1.56/0.60    spl6_1 | ~spl6_54),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f960])).
% 1.56/0.60  fof(f960,plain,(
% 1.56/0.60    $false | (spl6_1 | ~spl6_54)),
% 1.56/0.60    inference(resolution,[],[f896,f243])).
% 1.56/0.60  fof(f243,plain,(
% 1.56/0.60    v2_funct_1(k1_xboole_0)),
% 1.56/0.60    inference(superposition,[],[f104,f178])).
% 1.56/0.60  fof(f178,plain,(
% 1.56/0.60    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.56/0.60    inference(resolution,[],[f170,f150])).
% 1.56/0.60  fof(f150,plain,(
% 1.56/0.60    ( ! [X0] : (r1_tarski(k6_partfun1(k1_xboole_0),X0)) )),
% 1.56/0.60    inference(resolution,[],[f148,f93])).
% 1.56/0.60  fof(f93,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f59])).
% 1.56/0.60  fof(f59,plain,(
% 1.56/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).
% 1.56/0.60  fof(f58,plain,(
% 1.56/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.56/0.60    introduced(choice_axiom,[])).
% 1.56/0.60  fof(f57,plain,(
% 1.56/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.60    inference(rectify,[],[f56])).
% 1.56/0.60  fof(f56,plain,(
% 1.56/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.60    inference(nnf_transformation,[],[f35])).
% 1.56/0.60  fof(f35,plain,(
% 1.56/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.60    inference(ennf_transformation,[],[f2])).
% 1.56/0.60  fof(f2,axiom,(
% 1.56/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.60  fof(f148,plain,(
% 1.56/0.60    ( ! [X2] : (~r2_hidden(X2,k6_partfun1(k1_xboole_0))) )),
% 1.56/0.60    inference(resolution,[],[f145,f80])).
% 1.56/0.60  fof(f80,plain,(
% 1.56/0.60    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f51])).
% 1.56/0.60  fof(f51,plain,(
% 1.56/0.60    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.56/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 1.56/0.60  fof(f50,plain,(
% 1.56/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.56/0.60    introduced(choice_axiom,[])).
% 1.56/0.60  fof(f49,plain,(
% 1.56/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.56/0.60    inference(rectify,[],[f48])).
% 1.56/0.60  fof(f48,plain,(
% 1.56/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.56/0.60    inference(nnf_transformation,[],[f1])).
% 1.56/0.60  fof(f1,axiom,(
% 1.56/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.56/0.60  fof(f145,plain,(
% 1.56/0.60    v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 1.56/0.60    inference(resolution,[],[f131,f74])).
% 1.56/0.60  fof(f74,plain,(
% 1.56/0.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.56/0.60    inference(cnf_transformation,[],[f18])).
% 1.56/0.60  fof(f18,axiom,(
% 1.56/0.60    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.56/0.60  fof(f131,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) )),
% 1.56/0.60    inference(resolution,[],[f126,f77])).
% 1.56/0.60  fof(f77,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f26])).
% 1.56/0.60  fof(f26,plain,(
% 1.56/0.60    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.56/0.60    inference(ennf_transformation,[],[f7])).
% 1.56/0.60  fof(f7,axiom,(
% 1.56/0.60    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.56/0.60  fof(f126,plain,(
% 1.56/0.60    ( ! [X1] : (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1))) )),
% 1.56/0.60    inference(resolution,[],[f124,f84])).
% 1.56/0.60  fof(f84,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 1.56/0.60    inference(cnf_transformation,[],[f31])).
% 1.56/0.60  fof(f31,plain,(
% 1.56/0.60    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.56/0.60    inference(ennf_transformation,[],[f6])).
% 1.56/0.60  fof(f6,axiom,(
% 1.56/0.60    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.56/0.60  fof(f124,plain,(
% 1.56/0.60    v1_xboole_0(k1_xboole_0)),
% 1.56/0.60    inference(resolution,[],[f123,f109])).
% 1.56/0.60  fof(f109,plain,(
% 1.56/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.60    inference(equality_resolution,[],[f90])).
% 1.56/0.60  fof(f90,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.60    inference(cnf_transformation,[],[f55])).
% 1.56/0.60  fof(f55,plain,(
% 1.56/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.60    inference(flattening,[],[f54])).
% 1.56/0.60  fof(f54,plain,(
% 1.56/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.60    inference(nnf_transformation,[],[f3])).
% 1.56/0.60  fof(f3,axiom,(
% 1.56/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.60  fof(f123,plain,(
% 1.56/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 1.56/0.60    inference(resolution,[],[f83,f69])).
% 1.56/0.60  fof(f69,plain,(
% 1.56/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f4])).
% 1.56/0.60  fof(f4,axiom,(
% 1.56/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.56/0.60  fof(f83,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f30])).
% 1.56/0.60  fof(f30,plain,(
% 1.56/0.60    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.56/0.60    inference(flattening,[],[f29])).
% 1.56/0.60  fof(f29,plain,(
% 1.56/0.60    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.56/0.60    inference(ennf_transformation,[],[f5])).
% 1.56/0.60  fof(f5,axiom,(
% 1.56/0.60    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.56/0.60  fof(f170,plain,(
% 1.56/0.60    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.56/0.60    inference(resolution,[],[f91,f129])).
% 1.56/0.60  fof(f129,plain,(
% 1.56/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.56/0.60    inference(resolution,[],[f127,f93])).
% 1.56/0.60  fof(f127,plain,(
% 1.56/0.60    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 1.56/0.60    inference(resolution,[],[f124,f80])).
% 1.56/0.60  fof(f91,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f55])).
% 1.56/0.60  fof(f104,plain,(
% 1.56/0.60    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.56/0.60    inference(definition_unfolding,[],[f72,f70])).
% 1.56/0.60  fof(f70,plain,(
% 1.56/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f20])).
% 1.56/0.60  fof(f20,axiom,(
% 1.56/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.56/0.60  fof(f72,plain,(
% 1.56/0.60    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.56/0.60    inference(cnf_transformation,[],[f13])).
% 1.56/0.60  fof(f13,axiom,(
% 1.56/0.60    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.56/0.60  fof(f896,plain,(
% 1.56/0.60    ~v2_funct_1(k1_xboole_0) | (spl6_1 | ~spl6_54)),
% 1.56/0.60    inference(backward_demodulation,[],[f117,f891])).
% 1.56/0.60  fof(f891,plain,(
% 1.56/0.60    k1_xboole_0 = sK2 | ~spl6_54),
% 1.56/0.60    inference(resolution,[],[f890,f170])).
% 1.56/0.60  fof(f890,plain,(
% 1.56/0.60    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl6_54),
% 1.56/0.60    inference(resolution,[],[f888,f93])).
% 1.56/0.60  fof(f888,plain,(
% 1.56/0.60    ( ! [X2] : (~r2_hidden(X2,sK2)) ) | ~spl6_54),
% 1.56/0.60    inference(resolution,[],[f880,f80])).
% 1.56/0.60  fof(f880,plain,(
% 1.56/0.60    v1_xboole_0(sK2) | ~spl6_54),
% 1.56/0.60    inference(resolution,[],[f854,f125])).
% 1.56/0.60  fof(f125,plain,(
% 1.56/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 1.56/0.60    inference(resolution,[],[f124,f77])).
% 1.56/0.60  fof(f854,plain,(
% 1.56/0.60    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_54),
% 1.56/0.60    inference(forward_demodulation,[],[f833,f179])).
% 1.56/0.60  fof(f179,plain,(
% 1.56/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.56/0.60    inference(resolution,[],[f170,f135])).
% 1.56/0.60  fof(f135,plain,(
% 1.56/0.60    ( ! [X2,X1] : (r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2)) )),
% 1.56/0.60    inference(resolution,[],[f133,f93])).
% 1.56/0.60  fof(f133,plain,(
% 1.56/0.60    ( ! [X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(k1_xboole_0,X5))) )),
% 1.56/0.60    inference(resolution,[],[f126,f80])).
% 1.56/0.60  fof(f833,plain,(
% 1.56/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl6_54),
% 1.56/0.60    inference(backward_demodulation,[],[f63,f811])).
% 1.56/0.60  fof(f811,plain,(
% 1.56/0.60    k1_xboole_0 = sK0 | ~spl6_54),
% 1.56/0.60    inference(avatar_component_clause,[],[f809])).
% 1.56/0.60  fof(f809,plain,(
% 1.56/0.60    spl6_54 <=> k1_xboole_0 = sK0),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 1.56/0.60  fof(f63,plain,(
% 1.56/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.56/0.60    inference(cnf_transformation,[],[f47])).
% 1.56/0.60  fof(f47,plain,(
% 1.56/0.60    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.56/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f46,f45])).
% 1.56/0.60  fof(f45,plain,(
% 1.56/0.60    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.56/0.60    introduced(choice_axiom,[])).
% 1.56/0.60  fof(f46,plain,(
% 1.56/0.60    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.56/0.60    introduced(choice_axiom,[])).
% 1.56/0.60  fof(f25,plain,(
% 1.56/0.60    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.56/0.60    inference(flattening,[],[f24])).
% 1.56/0.60  fof(f24,plain,(
% 1.56/0.60    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.56/0.60    inference(ennf_transformation,[],[f23])).
% 1.56/0.60  fof(f23,negated_conjecture,(
% 1.56/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.56/0.60    inference(negated_conjecture,[],[f22])).
% 1.56/0.60  fof(f22,conjecture,(
% 1.56/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.56/0.60  fof(f117,plain,(
% 1.56/0.60    ~v2_funct_1(sK2) | spl6_1),
% 1.56/0.60    inference(avatar_component_clause,[],[f115])).
% 1.56/0.60  fof(f115,plain,(
% 1.56/0.60    spl6_1 <=> v2_funct_1(sK2)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.56/0.60  fof(f831,plain,(
% 1.56/0.60    spl6_55),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f829])).
% 1.56/0.60  fof(f829,plain,(
% 1.56/0.60    $false | spl6_55),
% 1.56/0.60    inference(resolution,[],[f815,f104])).
% 1.56/0.60  fof(f815,plain,(
% 1.56/0.60    ~v2_funct_1(k6_partfun1(sK0)) | spl6_55),
% 1.56/0.60    inference(avatar_component_clause,[],[f813])).
% 1.56/0.60  fof(f813,plain,(
% 1.56/0.60    spl6_55 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 1.56/0.60  fof(f816,plain,(
% 1.56/0.60    spl6_54 | ~spl6_23 | ~spl6_24 | ~spl6_55 | ~spl6_14 | ~spl6_53),
% 1.56/0.60    inference(avatar_split_clause,[],[f807,f787,f377,f813,f491,f487,f809])).
% 1.56/0.60  fof(f487,plain,(
% 1.56/0.60    spl6_23 <=> v1_funct_1(sK3)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.56/0.60  fof(f491,plain,(
% 1.56/0.60    spl6_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.56/0.60  fof(f377,plain,(
% 1.56/0.60    spl6_14 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.56/0.60  fof(f787,plain,(
% 1.56/0.60    spl6_53 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK1,X0))),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 1.56/0.60  fof(f807,plain,(
% 1.56/0.60    ~v2_funct_1(k6_partfun1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK0 | (~spl6_14 | ~spl6_53)),
% 1.56/0.60    inference(forward_demodulation,[],[f806,f379])).
% 1.56/0.60  fof(f379,plain,(
% 1.56/0.60    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl6_14),
% 1.56/0.60    inference(avatar_component_clause,[],[f377])).
% 1.56/0.60  fof(f806,plain,(
% 1.56/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK0 | ~spl6_53),
% 1.56/0.60    inference(resolution,[],[f788,f65])).
% 1.56/0.60  fof(f65,plain,(
% 1.56/0.60    v1_funct_2(sK3,sK1,sK0)),
% 1.56/0.60    inference(cnf_transformation,[],[f47])).
% 1.56/0.60  fof(f788,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~v1_funct_2(X1,sK1,X0) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(X1) | k1_xboole_0 = X0) ) | ~spl6_53),
% 1.56/0.60    inference(avatar_component_clause,[],[f787])).
% 1.56/0.60  fof(f789,plain,(
% 1.56/0.60    ~spl6_22 | spl6_53 | ~spl6_33),
% 1.56/0.60    inference(avatar_split_clause,[],[f785,f566,f787,f483])).
% 1.56/0.60  fof(f483,plain,(
% 1.56/0.60    spl6_22 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.56/0.60  fof(f566,plain,(
% 1.56/0.60    spl6_33 <=> ! [X1,X3,X0,X2] : (k1_xboole_0 = X0 | ~v1_funct_2(sK2,X1,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)))),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.56/0.60  fof(f785,plain,(
% 1.56/0.60    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))) ) | ~spl6_33),
% 1.56/0.60    inference(resolution,[],[f567,f62])).
% 1.56/0.60  fof(f62,plain,(
% 1.56/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.56/0.60    inference(cnf_transformation,[],[f47])).
% 1.56/0.60  fof(f567,plain,(
% 1.56/0.60    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK2,X1,X2) | k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3))) ) | ~spl6_33),
% 1.56/0.60    inference(avatar_component_clause,[],[f566])).
% 1.56/0.60  fof(f776,plain,(
% 1.56/0.60    spl6_52),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f775])).
% 1.56/0.60  fof(f775,plain,(
% 1.56/0.60    $false | spl6_52),
% 1.56/0.60    inference(resolution,[],[f773,f109])).
% 1.56/0.60  fof(f773,plain,(
% 1.56/0.60    ~r1_tarski(sK0,sK0) | spl6_52),
% 1.56/0.60    inference(avatar_component_clause,[],[f771])).
% 1.56/0.60  fof(f771,plain,(
% 1.56/0.60    spl6_52 <=> r1_tarski(sK0,sK0)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 1.56/0.60  fof(f774,plain,(
% 1.56/0.60    ~spl6_31 | ~spl6_52 | ~spl6_35 | spl6_51),
% 1.56/0.60    inference(avatar_split_clause,[],[f769,f763,f599,f771,f553])).
% 1.56/0.60  fof(f553,plain,(
% 1.56/0.60    spl6_31 <=> v1_relat_1(sK3)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.56/0.60  fof(f599,plain,(
% 1.56/0.60    spl6_35 <=> sK0 = k2_relat_1(sK3)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.56/0.60  fof(f763,plain,(
% 1.56/0.60    spl6_51 <=> v5_relat_1(sK3,sK0)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 1.56/0.60  fof(f769,plain,(
% 1.56/0.60    ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK3) | (~spl6_35 | spl6_51)),
% 1.56/0.60    inference(forward_demodulation,[],[f768,f601])).
% 1.56/0.60  fof(f601,plain,(
% 1.56/0.60    sK0 = k2_relat_1(sK3) | ~spl6_35),
% 1.56/0.60    inference(avatar_component_clause,[],[f599])).
% 1.56/0.60  fof(f768,plain,(
% 1.56/0.60    ~r1_tarski(k2_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | spl6_51),
% 1.56/0.60    inference(resolution,[],[f765,f86])).
% 1.56/0.60  fof(f86,plain,(
% 1.56/0.60    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f52])).
% 1.56/0.60  fof(f52,plain,(
% 1.56/0.60    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.56/0.60    inference(nnf_transformation,[],[f32])).
% 1.56/0.60  fof(f32,plain,(
% 1.56/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.56/0.60    inference(ennf_transformation,[],[f9])).
% 1.56/0.60  fof(f9,axiom,(
% 1.56/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.56/0.60  fof(f765,plain,(
% 1.56/0.60    ~v5_relat_1(sK3,sK0) | spl6_51),
% 1.56/0.60    inference(avatar_component_clause,[],[f763])).
% 1.56/0.60  fof(f766,plain,(
% 1.56/0.60    ~spl6_31 | ~spl6_51 | spl6_2 | ~spl6_35),
% 1.56/0.60    inference(avatar_split_clause,[],[f757,f599,f119,f763,f553])).
% 1.56/0.60  fof(f119,plain,(
% 1.56/0.60    spl6_2 <=> v2_funct_2(sK3,sK0)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.56/0.60  fof(f757,plain,(
% 1.56/0.60    v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl6_35),
% 1.56/0.60    inference(superposition,[],[f108,f601])).
% 1.56/0.60  fof(f108,plain,(
% 1.56/0.60    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.56/0.60    inference(equality_resolution,[],[f88])).
% 1.56/0.60  fof(f88,plain,(
% 1.56/0.60    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f53])).
% 1.56/0.60  fof(f53,plain,(
% 1.56/0.60    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.56/0.60    inference(nnf_transformation,[],[f34])).
% 1.56/0.60  fof(f34,plain,(
% 1.56/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.56/0.60    inference(flattening,[],[f33])).
% 1.56/0.60  fof(f33,plain,(
% 1.56/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.56/0.60    inference(ennf_transformation,[],[f16])).
% 1.56/0.60  fof(f16,axiom,(
% 1.56/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.56/0.60  fof(f741,plain,(
% 1.56/0.60    ~spl6_31 | spl6_34),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f738])).
% 1.56/0.60  fof(f738,plain,(
% 1.56/0.60    $false | (~spl6_31 | spl6_34)),
% 1.56/0.60    inference(resolution,[],[f736,f597])).
% 1.56/0.60  fof(f597,plain,(
% 1.56/0.60    ~r1_tarski(k2_relat_1(sK3),sK0) | spl6_34),
% 1.56/0.60    inference(avatar_component_clause,[],[f595])).
% 1.56/0.60  fof(f595,plain,(
% 1.56/0.60    spl6_34 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.56/0.60  fof(f736,plain,(
% 1.56/0.60    r1_tarski(k2_relat_1(sK3),sK0) | ~spl6_31),
% 1.56/0.60    inference(resolution,[],[f585,f66])).
% 1.56/0.60  fof(f66,plain,(
% 1.56/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.56/0.60    inference(cnf_transformation,[],[f47])).
% 1.56/0.60  fof(f585,plain,(
% 1.56/0.60    ( ! [X2,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r1_tarski(k2_relat_1(sK3),X1)) ) | ~spl6_31),
% 1.56/0.60    inference(resolution,[],[f554,f251])).
% 1.56/0.60  fof(f251,plain,(
% 1.56/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.56/0.60    inference(resolution,[],[f96,f85])).
% 1.56/0.60  fof(f85,plain,(
% 1.56/0.60    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f52])).
% 1.56/0.60  fof(f96,plain,(
% 1.56/0.60    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/0.60    inference(cnf_transformation,[],[f36])).
% 1.56/0.60  fof(f36,plain,(
% 1.56/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.60    inference(ennf_transformation,[],[f14])).
% 1.56/0.60  fof(f14,axiom,(
% 1.56/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.56/0.60  fof(f554,plain,(
% 1.56/0.60    v1_relat_1(sK3) | ~spl6_31),
% 1.56/0.60    inference(avatar_component_clause,[],[f553])).
% 1.56/0.60  fof(f602,plain,(
% 1.56/0.60    ~spl6_34 | spl6_35 | ~spl6_32),
% 1.56/0.60    inference(avatar_split_clause,[],[f593,f557,f599,f595])).
% 1.56/0.60  fof(f557,plain,(
% 1.56/0.60    spl6_32 <=> r1_tarski(sK0,k2_relat_1(sK3))),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.56/0.60  fof(f593,plain,(
% 1.56/0.60    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0) | ~spl6_32),
% 1.56/0.60    inference(resolution,[],[f559,f91])).
% 1.56/0.60  fof(f559,plain,(
% 1.56/0.60    r1_tarski(sK0,k2_relat_1(sK3)) | ~spl6_32),
% 1.56/0.60    inference(avatar_component_clause,[],[f557])).
% 1.56/0.60  fof(f583,plain,(
% 1.56/0.60    spl6_31),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f581])).
% 1.56/0.60  fof(f581,plain,(
% 1.56/0.60    $false | spl6_31),
% 1.56/0.60    inference(resolution,[],[f580,f82])).
% 1.56/0.60  fof(f82,plain,(
% 1.56/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.56/0.60    inference(cnf_transformation,[],[f10])).
% 1.56/0.60  fof(f10,axiom,(
% 1.56/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.56/0.60  fof(f580,plain,(
% 1.56/0.60    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl6_31),
% 1.56/0.60    inference(resolution,[],[f562,f66])).
% 1.56/0.60  fof(f562,plain,(
% 1.56/0.60    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_31),
% 1.56/0.60    inference(resolution,[],[f555,f79])).
% 1.56/0.60  fof(f79,plain,(
% 1.56/0.60    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f28])).
% 1.56/0.60  fof(f28,plain,(
% 1.56/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.56/0.60    inference(ennf_transformation,[],[f8])).
% 1.56/0.60  fof(f8,axiom,(
% 1.56/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.56/0.60  fof(f555,plain,(
% 1.56/0.60    ~v1_relat_1(sK3) | spl6_31),
% 1.56/0.60    inference(avatar_component_clause,[],[f553])).
% 1.56/0.60  fof(f571,plain,(
% 1.56/0.60    spl6_30),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f569])).
% 1.56/0.60  fof(f569,plain,(
% 1.56/0.60    $false | spl6_30),
% 1.56/0.60    inference(resolution,[],[f563,f82])).
% 1.56/0.60  fof(f563,plain,(
% 1.56/0.60    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl6_30),
% 1.56/0.60    inference(resolution,[],[f561,f63])).
% 1.56/0.60  fof(f561,plain,(
% 1.56/0.60    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_30),
% 1.56/0.60    inference(resolution,[],[f551,f79])).
% 1.56/0.60  fof(f551,plain,(
% 1.56/0.60    ~v1_relat_1(sK2) | spl6_30),
% 1.56/0.60    inference(avatar_component_clause,[],[f549])).
% 1.56/0.60  fof(f549,plain,(
% 1.56/0.60    spl6_30 <=> v1_relat_1(sK2)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.56/0.60  fof(f568,plain,(
% 1.56/0.60    ~spl6_17 | spl6_33 | spl6_1),
% 1.56/0.60    inference(avatar_split_clause,[],[f564,f115,f566,f452])).
% 1.56/0.60  fof(f452,plain,(
% 1.56/0.60    spl6_17 <=> v1_funct_1(sK2)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.56/0.60  fof(f564,plain,(
% 1.56/0.60    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~v2_funct_1(k1_partfun1(X1,X2,X2,X0,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X3,X2,X0) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK2,X1,X2) | ~v1_funct_1(sK2)) ) | spl6_1),
% 1.56/0.60    inference(resolution,[],[f97,f117])).
% 1.56/0.60  fof(f97,plain,(
% 1.56/0.60    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f38])).
% 1.56/0.60  fof(f38,plain,(
% 1.56/0.60    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.56/0.60    inference(flattening,[],[f37])).
% 1.56/0.60  fof(f37,plain,(
% 1.56/0.60    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.56/0.60    inference(ennf_transformation,[],[f21])).
% 1.56/0.60  fof(f21,axiom,(
% 1.56/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 1.56/0.60  fof(f560,plain,(
% 1.56/0.60    ~spl6_30 | ~spl6_31 | spl6_32 | ~spl6_27),
% 1.56/0.60    inference(avatar_split_clause,[],[f547,f533,f557,f553,f549])).
% 1.56/0.60  fof(f533,plain,(
% 1.56/0.60    spl6_27 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.56/0.60  fof(f547,plain,(
% 1.56/0.60    r1_tarski(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl6_27),
% 1.56/0.60    inference(forward_demodulation,[],[f546,f106])).
% 1.56/0.60  fof(f106,plain,(
% 1.56/0.60    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.56/0.60    inference(definition_unfolding,[],[f76,f70])).
% 1.56/0.60  fof(f76,plain,(
% 1.56/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.56/0.60    inference(cnf_transformation,[],[f12])).
% 1.56/0.60  fof(f12,axiom,(
% 1.56/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.56/0.60  fof(f546,plain,(
% 1.56/0.60    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl6_27),
% 1.56/0.60    inference(superposition,[],[f78,f535])).
% 1.56/0.60  fof(f535,plain,(
% 1.56/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl6_27),
% 1.56/0.60    inference(avatar_component_clause,[],[f533])).
% 1.56/0.60  fof(f78,plain,(
% 1.56/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f27])).
% 1.56/0.60  fof(f27,plain,(
% 1.56/0.60    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.60    inference(ennf_transformation,[],[f11])).
% 1.56/0.60  fof(f11,axiom,(
% 1.56/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.56/0.60  fof(f545,plain,(
% 1.56/0.60    ~spl6_17 | ~spl6_22 | spl6_27 | ~spl6_14),
% 1.56/0.60    inference(avatar_split_clause,[],[f529,f377,f533,f483,f452])).
% 1.56/0.60  fof(f529,plain,(
% 1.56/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl6_14),
% 1.56/0.60    inference(superposition,[],[f379,f468])).
% 1.56/0.60  fof(f468,plain,(
% 1.56/0.60    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.56/0.60    inference(resolution,[],[f437,f66])).
% 1.56/0.60  fof(f437,plain,(
% 1.56/0.60    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_funct_1(X9)) )),
% 1.56/0.60    inference(resolution,[],[f101,f64])).
% 1.56/0.60  fof(f64,plain,(
% 1.56/0.60    v1_funct_1(sK3)),
% 1.56/0.60    inference(cnf_transformation,[],[f47])).
% 1.56/0.60  fof(f101,plain,(
% 1.56/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f42])).
% 1.56/0.60  fof(f42,plain,(
% 1.56/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.56/0.60    inference(flattening,[],[f41])).
% 1.56/0.60  fof(f41,plain,(
% 1.56/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.56/0.60    inference(ennf_transformation,[],[f19])).
% 1.56/0.60  fof(f19,axiom,(
% 1.56/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.56/0.60  fof(f505,plain,(
% 1.56/0.60    spl6_24),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f504])).
% 1.56/0.60  fof(f504,plain,(
% 1.56/0.60    $false | spl6_24),
% 1.56/0.60    inference(resolution,[],[f493,f66])).
% 1.56/0.60  fof(f493,plain,(
% 1.56/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_24),
% 1.56/0.60    inference(avatar_component_clause,[],[f491])).
% 1.56/0.60  fof(f503,plain,(
% 1.56/0.60    spl6_22),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f502])).
% 1.56/0.60  fof(f502,plain,(
% 1.56/0.60    $false | spl6_22),
% 1.56/0.60    inference(resolution,[],[f485,f63])).
% 1.56/0.60  fof(f485,plain,(
% 1.56/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_22),
% 1.56/0.60    inference(avatar_component_clause,[],[f483])).
% 1.56/0.60  fof(f501,plain,(
% 1.56/0.60    spl6_23),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f500])).
% 1.56/0.60  fof(f500,plain,(
% 1.56/0.60    $false | spl6_23),
% 1.56/0.60    inference(resolution,[],[f489,f64])).
% 1.56/0.60  fof(f489,plain,(
% 1.56/0.60    ~v1_funct_1(sK3) | spl6_23),
% 1.56/0.60    inference(avatar_component_clause,[],[f487])).
% 1.56/0.60  fof(f494,plain,(
% 1.56/0.60    ~spl6_17 | ~spl6_22 | ~spl6_23 | ~spl6_24 | spl6_12),
% 1.56/0.60    inference(avatar_split_clause,[],[f478,f369,f491,f487,f483,f452])).
% 1.56/0.60  fof(f369,plain,(
% 1.56/0.60    spl6_12 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.56/0.60  fof(f478,plain,(
% 1.56/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl6_12),
% 1.56/0.60    inference(resolution,[],[f103,f371])).
% 1.56/0.60  fof(f371,plain,(
% 1.56/0.60    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_12),
% 1.56/0.60    inference(avatar_component_clause,[],[f369])).
% 1.56/0.60  fof(f103,plain,(
% 1.56/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.56/0.60    inference(cnf_transformation,[],[f44])).
% 1.56/0.60  fof(f44,plain,(
% 1.56/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.56/0.60    inference(flattening,[],[f43])).
% 1.56/0.60  fof(f43,plain,(
% 1.56/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.56/0.60    inference(ennf_transformation,[],[f17])).
% 1.56/0.60  fof(f17,axiom,(
% 1.56/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.56/0.60  fof(f463,plain,(
% 1.56/0.60    spl6_17),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f462])).
% 1.56/0.60  fof(f462,plain,(
% 1.56/0.60    $false | spl6_17),
% 1.56/0.60    inference(resolution,[],[f454,f61])).
% 1.56/0.60  fof(f61,plain,(
% 1.56/0.60    v1_funct_1(sK2)),
% 1.56/0.60    inference(cnf_transformation,[],[f47])).
% 1.56/0.60  fof(f454,plain,(
% 1.56/0.60    ~v1_funct_1(sK2) | spl6_17),
% 1.56/0.60    inference(avatar_component_clause,[],[f452])).
% 1.56/0.60  fof(f382,plain,(
% 1.56/0.60    spl6_13),
% 1.56/0.60    inference(avatar_contradiction_clause,[],[f381])).
% 1.56/0.60  fof(f381,plain,(
% 1.56/0.60    $false | spl6_13),
% 1.56/0.60    inference(resolution,[],[f375,f74])).
% 1.56/0.60  fof(f375,plain,(
% 1.56/0.60    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_13),
% 1.56/0.60    inference(avatar_component_clause,[],[f373])).
% 1.56/0.60  fof(f373,plain,(
% 1.56/0.60    spl6_13 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.56/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.56/0.60  fof(f380,plain,(
% 1.56/0.60    ~spl6_12 | ~spl6_13 | spl6_14),
% 1.56/0.60    inference(avatar_split_clause,[],[f365,f377,f373,f369])).
% 1.56/0.60  fof(f365,plain,(
% 1.56/0.60    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.56/0.60    inference(resolution,[],[f99,f67])).
% 1.56/0.60  fof(f67,plain,(
% 1.56/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.56/0.60    inference(cnf_transformation,[],[f47])).
% 1.56/0.60  fof(f99,plain,(
% 1.56/0.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/0.60    inference(cnf_transformation,[],[f60])).
% 1.56/0.60  fof(f60,plain,(
% 1.56/0.60    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.60    inference(nnf_transformation,[],[f40])).
% 1.56/0.60  fof(f40,plain,(
% 1.56/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.60    inference(flattening,[],[f39])).
% 1.56/0.60  fof(f39,plain,(
% 1.56/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.56/0.60    inference(ennf_transformation,[],[f15])).
% 1.56/0.60  fof(f15,axiom,(
% 1.56/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.56/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.56/0.60  fof(f122,plain,(
% 1.56/0.60    ~spl6_1 | ~spl6_2),
% 1.56/0.60    inference(avatar_split_clause,[],[f68,f119,f115])).
% 1.56/0.60  fof(f68,plain,(
% 1.56/0.60    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.56/0.60    inference(cnf_transformation,[],[f47])).
% 1.56/0.60  % SZS output end Proof for theBenchmark
% 1.56/0.60  % (8423)------------------------------
% 1.56/0.60  % (8423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.60  % (8423)Termination reason: Refutation
% 1.56/0.60  
% 1.56/0.60  % (8423)Memory used [KB]: 6780
% 1.56/0.60  % (8423)Time elapsed: 0.161 s
% 1.56/0.60  % (8423)------------------------------
% 1.56/0.60  % (8423)------------------------------
% 1.56/0.60  % (8410)Success in time 0.237 s
%------------------------------------------------------------------------------
