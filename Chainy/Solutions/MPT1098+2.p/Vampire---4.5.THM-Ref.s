%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1098+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:06 EST 2020

% Result     : Theorem 45.21s
% Output     : Refutation 45.46s
% Verified   : 
% Statistics : Number of formulae       :   51 (  99 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  168 ( 373 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81240,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5265,f5270,f6880,f6885,f6895,f6900,f81231])).

fof(f81231,plain,
    ( ~ spl473_79
    | ~ spl473_80
    | ~ spl473_82
    | ~ spl473_83 ),
    inference(avatar_contradiction_clause,[],[f81230])).

fof(f81230,plain,
    ( $false
    | ~ spl473_79
    | ~ spl473_80
    | ~ spl473_82
    | ~ spl473_83 ),
    inference(subsumption_resolution,[],[f81065,f42892])).

fof(f42892,plain,
    ( ! [X0] : r1_tarski(k2_zfmisc_1(X0,sK9(sK0,sK1,sK2)),k2_zfmisc_1(X0,sK2))
    | ~ spl473_80 ),
    inference(unit_resulting_resolution,[],[f6884,f3144])).

fof(f3144,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1781])).

fof(f1781,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f334])).

fof(f334,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f6884,plain,
    ( r1_tarski(sK9(sK0,sK1,sK2),sK2)
    | ~ spl473_80 ),
    inference(avatar_component_clause,[],[f6882])).

fof(f6882,plain,
    ( spl473_80
  <=> r1_tarski(sK9(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl473_80])])).

fof(f81065,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK8(sK0,sK1,sK2),sK9(sK0,sK1,sK2)),k2_zfmisc_1(sK8(sK0,sK1,sK2),sK2))
    | ~ spl473_79
    | ~ spl473_82
    | ~ spl473_83 ),
    inference(unit_resulting_resolution,[],[f6879,f6899,f6894,f9209])).

fof(f9209,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X2,sK2))
      | ~ v1_finset_1(X2)
      | ~ r1_tarski(X2,sK1)
      | ~ r1_tarski(sK0,X3) ) ),
    inference(resolution,[],[f3138,f3142])).

fof(f3142,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1780])).

fof(f1780,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1779])).

fof(f1779,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f3138,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
      | ~ r1_tarski(X3,sK1)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f2567])).

fof(f2567,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
        | ~ r1_tarski(X3,sK1)
        | ~ v1_finset_1(X3) )
    & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1772,f2566])).

fof(f2566,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
            | ~ r1_tarski(X3,X1)
            | ~ v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) )
   => ( ! [X3] :
          ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
          | ~ r1_tarski(X3,sK1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1772,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1757])).

fof(f1757,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f1756])).

fof(f1756,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

fof(f6894,plain,
    ( r1_tarski(sK8(sK0,sK1,sK2),sK1)
    | ~ spl473_82 ),
    inference(avatar_component_clause,[],[f6892])).

fof(f6892,plain,
    ( spl473_82
  <=> r1_tarski(sK8(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl473_82])])).

fof(f6899,plain,
    ( v1_finset_1(sK8(sK0,sK1,sK2))
    | ~ spl473_83 ),
    inference(avatar_component_clause,[],[f6897])).

fof(f6897,plain,
    ( spl473_83
  <=> v1_finset_1(sK8(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl473_83])])).

fof(f6879,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK8(sK0,sK1,sK2),sK9(sK0,sK1,sK2)))
    | ~ spl473_79 ),
    inference(avatar_component_clause,[],[f6877])).

fof(f6877,plain,
    ( spl473_79
  <=> r1_tarski(sK0,k2_zfmisc_1(sK8(sK0,sK1,sK2),sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl473_79])])).

fof(f6900,plain,
    ( spl473_83
    | ~ spl473_1
    | ~ spl473_2 ),
    inference(avatar_split_clause,[],[f5431,f5267,f5262,f6897])).

fof(f5262,plain,
    ( spl473_1
  <=> r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl473_1])])).

fof(f5267,plain,
    ( spl473_2
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl473_2])])).

fof(f5431,plain,
    ( v1_finset_1(sK8(sK0,sK1,sK2))
    | ~ spl473_1
    | ~ spl473_2 ),
    inference(unit_resulting_resolution,[],[f5269,f5264,f3170])).

fof(f3170,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK8(X0,X1,X2))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f2586])).

fof(f2586,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_zfmisc_1(sK8(X0,X1,X2),sK9(X0,X1,X2)))
        & r1_tarski(sK9(X0,X1,X2),X2)
        & v1_finset_1(sK9(X0,X1,X2))
        & r1_tarski(sK8(X0,X1,X2),X1)
        & v1_finset_1(sK8(X0,X1,X2)) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f1791,f2585])).

fof(f2585,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
     => ( r1_tarski(X0,k2_zfmisc_1(sK8(X0,X1,X2),sK9(X0,X1,X2)))
        & r1_tarski(sK9(X0,X1,X2),X2)
        & v1_finset_1(sK9(X0,X1,X2))
        & r1_tarski(sK8(X0,X1,X2),X1)
        & v1_finset_1(sK8(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1791,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1755])).

fof(f1755,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
              & r1_tarski(X4,X2)
              & v1_finset_1(X4)
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

fof(f5264,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl473_1 ),
    inference(avatar_component_clause,[],[f5262])).

fof(f5269,plain,
    ( v1_finset_1(sK0)
    | ~ spl473_2 ),
    inference(avatar_component_clause,[],[f5267])).

fof(f6895,plain,
    ( spl473_82
    | ~ spl473_1
    | ~ spl473_2 ),
    inference(avatar_split_clause,[],[f5432,f5267,f5262,f6892])).

fof(f5432,plain,
    ( r1_tarski(sK8(sK0,sK1,sK2),sK1)
    | ~ spl473_1
    | ~ spl473_2 ),
    inference(unit_resulting_resolution,[],[f5269,f5264,f3171])).

fof(f3171,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK8(X0,X1,X2),X1)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f2586])).

fof(f6885,plain,
    ( spl473_80
    | ~ spl473_1
    | ~ spl473_2 ),
    inference(avatar_split_clause,[],[f5434,f5267,f5262,f6882])).

fof(f5434,plain,
    ( r1_tarski(sK9(sK0,sK1,sK2),sK2)
    | ~ spl473_1
    | ~ spl473_2 ),
    inference(unit_resulting_resolution,[],[f5269,f5264,f3173])).

fof(f3173,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK9(X0,X1,X2),X2)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f2586])).

fof(f6880,plain,
    ( spl473_79
    | ~ spl473_1
    | ~ spl473_2 ),
    inference(avatar_split_clause,[],[f5435,f5267,f5262,f6877])).

fof(f5435,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK8(sK0,sK1,sK2),sK9(sK0,sK1,sK2)))
    | ~ spl473_1
    | ~ spl473_2 ),
    inference(unit_resulting_resolution,[],[f5269,f5264,f3174])).

fof(f3174,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_zfmisc_1(sK8(X0,X1,X2),sK9(X0,X1,X2)))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f2586])).

fof(f5270,plain,(
    spl473_2 ),
    inference(avatar_split_clause,[],[f3136,f5267])).

fof(f3136,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f2567])).

fof(f5265,plain,(
    spl473_1 ),
    inference(avatar_split_clause,[],[f3137,f5262])).

fof(f3137,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f2567])).
%------------------------------------------------------------------------------
