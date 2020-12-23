%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:28 EST 2020

% Result     : Theorem 4.33s
% Output     : Refutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 389 expanded)
%              Number of leaves         :   34 ( 135 expanded)
%              Depth                    :   11
%              Number of atoms          :  551 (2095 expanded)
%              Number of equality atoms :   27 ( 216 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f213,f481,f932,f1258,f1268,f1285,f1591,f1872,f1886,f1887,f4220,f4242,f4249,f7703,f9741,f10120,f10135])).

fof(f10135,plain,
    ( ~ spl9_41
    | ~ spl9_96
    | ~ spl9_95 ),
    inference(avatar_split_clause,[],[f902,f1874,f1878,f675])).

fof(f675,plain,
    ( spl9_41
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f1878,plain,
    ( spl9_96
  <=> r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f1874,plain,
    ( spl9_95
  <=> r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).

fof(f902,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2))
    | ~ r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f141,f118])).

fof(f118,plain,(
    ~ sQ8_eqProxy(sK1,k3_subset_1(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f71,f117])).

fof(f117,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f71,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( sK1 != k3_subset_1(sK0,sK2)
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | r2_hidden(X3,sK2) )
          & ( ~ r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f40,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | r2_hidden(X3,X2) )
                  & ( ~ r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != k3_subset_1(sK0,X2)
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( sK1 != k3_subset_1(sK0,X2)
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | r2_hidden(X3,X2) )
              & ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != k3_subset_1(sK0,sK2)
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | r2_hidden(X3,sK2) )
            & ( ~ r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> ~ r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_subset_1)).

fof(f141,plain,(
    ! [X9] :
      ( sQ8_eqProxy(sK1,X9)
      | ~ r2_hidden(sK5(sK0,sK1,X9),X9)
      | ~ r2_hidden(sK5(sK0,sK1,X9),sK1)
      | ~ m1_subset_1(X9,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f67,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( sQ8_eqProxy(X1,X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f89,f117])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK5(X0,X1,X2),X2)
              | ~ r2_hidden(sK5(X0,X1,X2),X1) )
            & ( r2_hidden(sK5(X0,X1,X2),X2)
              | r2_hidden(sK5(X0,X1,X2),X1) )
            & m1_subset_1(sK5(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X2)
          | ~ r2_hidden(sK5(X0,X1,X2),X1) )
        & ( r2_hidden(sK5(X0,X1,X2),X2)
          | r2_hidden(sK5(X0,X1,X2),X1) )
        & m1_subset_1(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f10120,plain,
    ( ~ spl9_96
    | spl9_95
    | ~ spl9_248 ),
    inference(avatar_split_clause,[],[f10110,f4218,f1874,f1878])).

fof(f4218,plain,
    ( spl9_248
  <=> ! [X11] :
        ( r2_hidden(X11,k3_subset_1(sK0,sK2))
        | ~ r2_hidden(X11,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_248])])).

fof(f10110,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK1)
    | spl9_95
    | ~ spl9_248 ),
    inference(resolution,[],[f4219,f1875])).

fof(f1875,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2))
    | spl9_95 ),
    inference(avatar_component_clause,[],[f1874])).

fof(f4219,plain,
    ( ! [X11] :
        ( r2_hidden(X11,k3_subset_1(sK0,sK2))
        | ~ r2_hidden(X11,sK1) )
    | ~ spl9_248 ),
    inference(avatar_component_clause,[],[f4218])).

fof(f9741,plain,
    ( spl9_86
    | spl9_253 ),
    inference(avatar_contradiction_clause,[],[f9731])).

fof(f9731,plain,
    ( $false
    | spl9_86
    | spl9_253 ),
    inference(resolution,[],[f5634,f1859])).

fof(f1859,plain,
    ( r2_hidden(sK4(sK2,sK1),sK2)
    | spl9_86 ),
    inference(resolution,[],[f1589,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1589,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl9_86 ),
    inference(avatar_component_clause,[],[f1587])).

fof(f1587,plain,
    ( spl9_86
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f5634,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK2)
    | spl9_253 ),
    inference(resolution,[],[f4241,f168])).

fof(f168,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f68,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

% (22893)Termination reason: Time limit

% (22893)Memory used [KB]: 8955
% (22893)Time elapsed: 0.538 s
% (22893)------------------------------
% (22893)------------------------------
fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f4241,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK0)
    | spl9_253 ),
    inference(avatar_component_clause,[],[f4239])).

fof(f4239,plain,
    ( spl9_253
  <=> r2_hidden(sK4(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_253])])).

fof(f7703,plain,
    ( ~ spl9_97
    | ~ spl9_72
    | ~ spl9_95 ),
    inference(avatar_split_clause,[],[f7687,f1874,f1281,f1883])).

fof(f1883,plain,
    ( spl9_97
  <=> r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).

fof(f1281,plain,
    ( spl9_72
  <=> r1_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f7687,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK2)
    | ~ spl9_72
    | ~ spl9_95 ),
    inference(resolution,[],[f1607,f1876])).

fof(f1876,plain,
    ( r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2))
    | ~ spl9_95 ),
    inference(avatar_component_clause,[],[f1874])).

fof(f1607,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k3_subset_1(sK0,sK2))
        | ~ r2_hidden(X4,sK2) )
    | ~ spl9_72 ),
    inference(resolution,[],[f1283,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1283,plain,
    ( r1_xboole_0(sK2,k3_subset_1(sK0,sK2))
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f1281])).

fof(f4249,plain,
    ( spl9_14
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f3053,f954,f270])).

fof(f270,plain,
    ( spl9_14
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f954,plain,
    ( spl9_58
  <=> r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f3053,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f631,f68])).

fof(f631,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(sK0))
      | ~ r1_tarski(X8,k3_subset_1(sK0,sK1))
      | r1_xboole_0(sK1,X8) ) ),
    inference(resolution,[],[f136,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f136,plain,(
    ! [X4] :
      ( r1_xboole_0(X4,sK1)
      | ~ r1_tarski(X4,k3_subset_1(sK0,sK1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f67,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f4242,plain,
    ( spl9_86
    | ~ spl9_253
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f3227,f211,f4239,f1587])).

fof(f211,plain,
    ( spl9_8
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f3227,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK0)
    | r1_xboole_0(sK2,sK1)
    | ~ spl9_8 ),
    inference(duplicate_literal_removal,[],[f3221])).

fof(f3221,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK0)
    | r1_xboole_0(sK2,sK1)
    | r1_xboole_0(sK2,sK1)
    | ~ spl9_8 ),
    inference(resolution,[],[f442,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f442,plain,
    ( ! [X10] :
        ( ~ r2_hidden(sK4(sK2,X10),sK1)
        | ~ r2_hidden(sK4(sK2,X10),sK0)
        | r1_xboole_0(sK2,X10) )
    | ~ spl9_8 ),
    inference(resolution,[],[f212,f80])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f211])).

fof(f4220,plain,
    ( spl9_248
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f3549,f270,f4218])).

fof(f3549,plain,(
    ! [X11] :
      ( ~ r1_xboole_0(sK1,sK2)
      | r2_hidden(X11,k3_subset_1(sK0,sK2))
      | ~ r2_hidden(X11,sK1) ) ),
    inference(resolution,[],[f558,f68])).

fof(f558,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r1_xboole_0(sK1,X3)
      | r2_hidden(X4,k3_subset_1(sK0,X3))
      | ~ r2_hidden(X4,sK1) ) ),
    inference(resolution,[],[f133,f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f133,plain,(
    ! [X1] :
      ( r1_tarski(sK1,k3_subset_1(sK0,X1))
      | ~ r1_xboole_0(sK1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f67,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1887,plain,
    ( ~ spl9_41
    | spl9_96
    | spl9_95 ),
    inference(avatar_split_clause,[],[f913,f1874,f1878,f675])).

fof(f913,plain,
    ( r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2))
    | r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f143,f118])).

fof(f143,plain,(
    ! [X11] :
      ( sQ8_eqProxy(sK1,X11)
      | r2_hidden(sK5(sK0,sK1,X11),X11)
      | r2_hidden(sK5(sK0,sK1,X11),sK1)
      | ~ m1_subset_1(X11,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f67,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( sQ8_eqProxy(X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f88,f117])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1886,plain,
    ( ~ spl9_12
    | ~ spl9_41
    | spl9_97
    | spl9_96 ),
    inference(avatar_split_clause,[],[f1050,f1878,f1883,f675,f262])).

fof(f262,plain,
    ( spl9_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f1050,plain,
    ( r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK1)
    | r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK2)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f224,f118])).

fof(f224,plain,(
    ! [X2,X3] :
      ( sQ8_eqProxy(X2,X3)
      | r2_hidden(sK5(sK0,X2,X3),sK1)
      | r2_hidden(sK5(sK0,X2,X3),sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f70,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( sQ8_eqProxy(X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f87,f117])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK5(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1872,plain,(
    spl9_41 ),
    inference(avatar_contradiction_clause,[],[f1868])).

fof(f1868,plain,
    ( $false
    | spl9_41 ),
    inference(resolution,[],[f677,f167])).

fof(f167,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f68,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f677,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl9_41 ),
    inference(avatar_component_clause,[],[f675])).

fof(f1591,plain,
    ( ~ spl9_13
    | ~ spl9_86
    | spl9_58 ),
    inference(avatar_split_clause,[],[f1581,f954,f1587,f266])).

fof(f266,plain,
    ( spl9_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f1581,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl9_58 ),
    inference(resolution,[],[f955,f134])).

fof(f134,plain,(
    ! [X2] :
      ( r1_tarski(X2,k3_subset_1(sK0,sK1))
      | ~ r1_xboole_0(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f67,f90])).

fof(f955,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | spl9_58 ),
    inference(avatar_component_clause,[],[f954])).

fof(f1285,plain,
    ( ~ spl9_13
    | spl9_72 ),
    inference(avatar_split_clause,[],[f869,f1281,f266])).

fof(f869,plain,
    ( r1_xboole_0(sK2,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f176,f113])).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f176,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,sK2)
      | r1_xboole_0(X8,k3_subset_1(sK0,sK2))
      | ~ m1_subset_1(X8,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f68,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f1268,plain,(
    spl9_13 ),
    inference(avatar_contradiction_clause,[],[f1265])).

fof(f1265,plain,
    ( $false
    | spl9_13 ),
    inference(resolution,[],[f268,f68])).

fof(f268,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl9_13 ),
    inference(avatar_component_clause,[],[f266])).

fof(f1258,plain,(
    spl9_12 ),
    inference(avatar_contradiction_clause,[],[f1255])).

fof(f1255,plain,
    ( $false
    | spl9_12 ),
    inference(resolution,[],[f264,f67])).

fof(f264,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f262])).

fof(f932,plain,
    ( spl9_14
    | ~ spl9_23 ),
    inference(avatar_contradiction_clause,[],[f929])).

fof(f929,plain,
    ( $false
    | spl9_14
    | ~ spl9_23 ),
    inference(resolution,[],[f570,f272])).

fof(f272,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl9_14 ),
    inference(avatar_component_clause,[],[f270])).

fof(f570,plain,
    ( ! [X10] : r1_xboole_0(X10,sK2)
    | ~ spl9_23 ),
    inference(resolution,[],[f480,f81])).

fof(f480,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f479])).

fof(f479,plain,
    ( spl9_23
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f481,plain,
    ( ~ spl9_7
    | spl9_23 ),
    inference(avatar_split_clause,[],[f400,f479,f207])).

fof(f207,plain,
    ( spl9_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f400,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f168,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f213,plain,
    ( spl9_7
    | spl9_8 ),
    inference(avatar_split_clause,[],[f203,f211,f207])).

fof(f203,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f69,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f69,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (22903)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (22895)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (22887)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.50  % (22888)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (22896)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (22894)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (22893)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (22904)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (22900)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (22886)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (22881)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (22884)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (22898)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (22882)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (22883)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (22897)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (22885)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (22892)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (22908)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (22902)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (22907)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (22891)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (22905)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (22906)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (22899)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (22890)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (22889)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.55  % (22901)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.55  % (22909)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.55  % (22910)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.59/0.60  % (22891)Refutation not found, incomplete strategy% (22891)------------------------------
% 1.59/0.60  % (22891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.60  % (22891)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.60  
% 1.59/0.60  % (22891)Memory used [KB]: 11129
% 1.59/0.60  % (22891)Time elapsed: 0.196 s
% 1.59/0.60  % (22891)------------------------------
% 1.59/0.60  % (22891)------------------------------
% 2.84/0.75  % (22991)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.13/0.80  % (22886)Time limit reached!
% 3.13/0.80  % (22886)------------------------------
% 3.13/0.80  % (22886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.81  % (22886)Termination reason: Time limit
% 3.13/0.82  % (22886)Termination phase: Saturation
% 3.13/0.82  
% 3.13/0.82  % (22886)Memory used [KB]: 8059
% 3.13/0.82  % (22886)Time elapsed: 0.400 s
% 3.13/0.82  % (22886)------------------------------
% 3.13/0.82  % (22886)------------------------------
% 3.84/0.92  % (22898)Time limit reached!
% 3.84/0.92  % (22898)------------------------------
% 3.84/0.92  % (22898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.84/0.92  % (22881)Time limit reached!
% 3.84/0.92  % (22881)------------------------------
% 3.84/0.92  % (22881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.84/0.92  % (22881)Termination reason: Time limit
% 3.84/0.92  
% 3.84/0.92  % (22881)Memory used [KB]: 2814
% 3.84/0.92  % (22881)Time elapsed: 0.514 s
% 3.84/0.92  % (22881)------------------------------
% 3.84/0.92  % (22881)------------------------------
% 3.84/0.92  % (22882)Time limit reached!
% 3.84/0.92  % (22882)------------------------------
% 3.84/0.92  % (22882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.84/0.92  % (22882)Termination reason: Time limit
% 3.84/0.92  
% 3.84/0.92  % (22882)Memory used [KB]: 8315
% 3.84/0.92  % (22882)Time elapsed: 0.518 s
% 3.84/0.92  % (22882)------------------------------
% 3.84/0.92  % (22882)------------------------------
% 4.33/0.94  % (22893)Time limit reached!
% 4.33/0.94  % (22893)------------------------------
% 4.33/0.94  % (22893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.94  % (22898)Termination reason: Time limit
% 4.33/0.94  % (22898)Termination phase: Saturation
% 4.33/0.94  
% 4.33/0.94  % (22898)Memory used [KB]: 13432
% 4.33/0.94  % (22898)Time elapsed: 0.500 s
% 4.33/0.94  % (22898)------------------------------
% 4.33/0.94  % (22898)------------------------------
% 4.33/0.95  % (22896)Refutation found. Thanks to Tanya!
% 4.33/0.95  % SZS status Theorem for theBenchmark
% 4.33/0.95  % (23078)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.33/0.96  % SZS output start Proof for theBenchmark
% 4.58/0.96  fof(f10136,plain,(
% 4.58/0.96    $false),
% 4.58/0.96    inference(avatar_sat_refutation,[],[f213,f481,f932,f1258,f1268,f1285,f1591,f1872,f1886,f1887,f4220,f4242,f4249,f7703,f9741,f10120,f10135])).
% 4.58/0.96  fof(f10135,plain,(
% 4.58/0.96    ~spl9_41 | ~spl9_96 | ~spl9_95),
% 4.58/0.96    inference(avatar_split_clause,[],[f902,f1874,f1878,f675])).
% 4.58/0.96  fof(f675,plain,(
% 4.58/0.96    spl9_41 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 4.58/0.96  fof(f1878,plain,(
% 4.58/0.96    spl9_96 <=> r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK1)),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).
% 4.58/0.96  fof(f1874,plain,(
% 4.58/0.96    spl9_95 <=> r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2))),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).
% 4.58/0.96  fof(f902,plain,(
% 4.58/0.96    ~r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2)) | ~r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK1) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 4.58/0.96    inference(resolution,[],[f141,f118])).
% 4.58/0.96  fof(f118,plain,(
% 4.58/0.96    ~sQ8_eqProxy(sK1,k3_subset_1(sK0,sK2))),
% 4.58/0.96    inference(equality_proxy_replacement,[],[f71,f117])).
% 4.58/0.96  fof(f117,plain,(
% 4.58/0.96    ! [X1,X0] : (sQ8_eqProxy(X0,X1) <=> X0 = X1)),
% 4.58/0.96    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).
% 4.58/0.96  fof(f71,plain,(
% 4.58/0.96    sK1 != k3_subset_1(sK0,sK2)),
% 4.58/0.96    inference(cnf_transformation,[],[f41])).
% 4.58/0.96  fof(f41,plain,(
% 4.58/0.96    (sK1 != k3_subset_1(sK0,sK2) & ! [X3] : (((r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) & (~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 4.58/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f40,f39])).
% 4.58/0.96  fof(f39,plain,(
% 4.58/0.96    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != k3_subset_1(sK0,X2) & ! [X3] : (((r2_hidden(X3,sK1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 4.58/0.96    introduced(choice_axiom,[])).
% 4.58/0.96  fof(f40,plain,(
% 4.58/0.96    ? [X2] : (sK1 != k3_subset_1(sK0,X2) & ! [X3] : (((r2_hidden(X3,sK1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != k3_subset_1(sK0,sK2) & ! [X3] : (((r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) & (~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 4.58/0.96    introduced(choice_axiom,[])).
% 4.58/0.96  fof(f38,plain,(
% 4.58/0.96    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : (((r2_hidden(X3,X1) | r2_hidden(X3,X2)) & (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(nnf_transformation,[],[f23])).
% 4.58/0.96  fof(f23,plain,(
% 4.58/0.96    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(flattening,[],[f22])).
% 4.58/0.96  fof(f22,plain,(
% 4.58/0.96    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & ! [X3] : ((r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(ennf_transformation,[],[f20])).
% 4.58/0.96  fof(f20,negated_conjecture,(
% 4.58/0.96    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 4.58/0.96    inference(negated_conjecture,[],[f19])).
% 4.58/0.96  fof(f19,conjecture,(
% 4.58/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> ~r2_hidden(X3,X2))) => k3_subset_1(X0,X2) = X1)))),
% 4.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_subset_1)).
% 4.58/0.96  fof(f141,plain,(
% 4.58/0.96    ( ! [X9] : (sQ8_eqProxy(sK1,X9) | ~r2_hidden(sK5(sK0,sK1,X9),X9) | ~r2_hidden(sK5(sK0,sK1,X9),sK1) | ~m1_subset_1(X9,k1_zfmisc_1(sK0))) )),
% 4.58/0.96    inference(resolution,[],[f67,f121])).
% 4.58/0.96  fof(f121,plain,(
% 4.58/0.96    ( ! [X2,X0,X1] : (sQ8_eqProxy(X1,X2) | ~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.58/0.96    inference(equality_proxy_replacement,[],[f89,f117])).
% 4.58/0.96  fof(f89,plain,(
% 4.58/0.96    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.58/0.96    inference(cnf_transformation,[],[f52])).
% 4.58/0.96  fof(f52,plain,(
% 4.58/0.96    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1)) & (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1)) & m1_subset_1(sK5(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).
% 4.58/0.96  fof(f51,plain,(
% 4.58/0.96    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1)) & (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1)) & m1_subset_1(sK5(X0,X1,X2),X0)))),
% 4.58/0.96    introduced(choice_axiom,[])).
% 4.58/0.96  fof(f50,plain,(
% 4.58/0.96    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(flattening,[],[f49])).
% 4.58/0.96  fof(f49,plain,(
% 4.58/0.96    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(nnf_transformation,[],[f31])).
% 4.58/0.96  fof(f31,plain,(
% 4.58/0.96    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(flattening,[],[f30])).
% 4.58/0.96  fof(f30,plain,(
% 4.58/0.96    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(ennf_transformation,[],[f18])).
% 4.58/0.96  fof(f18,axiom,(
% 4.58/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 4.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 4.58/0.96  fof(f67,plain,(
% 4.58/0.96    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 4.58/0.96    inference(cnf_transformation,[],[f41])).
% 4.58/0.96  fof(f10120,plain,(
% 4.58/0.96    ~spl9_96 | spl9_95 | ~spl9_248),
% 4.58/0.96    inference(avatar_split_clause,[],[f10110,f4218,f1874,f1878])).
% 4.58/0.96  fof(f4218,plain,(
% 4.58/0.96    spl9_248 <=> ! [X11] : (r2_hidden(X11,k3_subset_1(sK0,sK2)) | ~r2_hidden(X11,sK1))),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_248])])).
% 4.58/0.96  fof(f10110,plain,(
% 4.58/0.96    ~r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK1) | (spl9_95 | ~spl9_248)),
% 4.58/0.96    inference(resolution,[],[f4219,f1875])).
% 4.58/0.96  fof(f1875,plain,(
% 4.58/0.96    ~r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2)) | spl9_95),
% 4.58/0.96    inference(avatar_component_clause,[],[f1874])).
% 4.58/0.96  fof(f4219,plain,(
% 4.58/0.96    ( ! [X11] : (r2_hidden(X11,k3_subset_1(sK0,sK2)) | ~r2_hidden(X11,sK1)) ) | ~spl9_248),
% 4.58/0.96    inference(avatar_component_clause,[],[f4218])).
% 4.58/0.96  fof(f9741,plain,(
% 4.58/0.96    spl9_86 | spl9_253),
% 4.58/0.96    inference(avatar_contradiction_clause,[],[f9731])).
% 4.58/0.96  fof(f9731,plain,(
% 4.58/0.96    $false | (spl9_86 | spl9_253)),
% 4.58/0.96    inference(resolution,[],[f5634,f1859])).
% 4.58/0.96  fof(f1859,plain,(
% 4.58/0.96    r2_hidden(sK4(sK2,sK1),sK2) | spl9_86),
% 4.58/0.96    inference(resolution,[],[f1589,f80])).
% 4.58/0.96  fof(f80,plain,(
% 4.58/0.96    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 4.58/0.96    inference(cnf_transformation,[],[f48])).
% 4.58/0.96  fof(f48,plain,(
% 4.58/0.96    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.58/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f47])).
% 4.58/0.96  fof(f47,plain,(
% 4.58/0.96    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 4.58/0.96    introduced(choice_axiom,[])).
% 4.58/0.96  fof(f25,plain,(
% 4.58/0.96    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.58/0.96    inference(ennf_transformation,[],[f21])).
% 4.58/0.96  fof(f21,plain,(
% 4.58/0.96    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.58/0.96    inference(rectify,[],[f6])).
% 4.58/0.96  fof(f6,axiom,(
% 4.58/0.96    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 4.58/0.96  fof(f1589,plain,(
% 4.58/0.96    ~r1_xboole_0(sK2,sK1) | spl9_86),
% 4.58/0.96    inference(avatar_component_clause,[],[f1587])).
% 4.58/0.96  fof(f1587,plain,(
% 4.58/0.96    spl9_86 <=> r1_xboole_0(sK2,sK1)),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).
% 4.58/0.96  fof(f5634,plain,(
% 4.58/0.96    ~r2_hidden(sK4(sK2,sK1),sK2) | spl9_253),
% 4.58/0.96    inference(resolution,[],[f4241,f168])).
% 4.58/0.96  fof(f168,plain,(
% 4.58/0.96    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK2)) )),
% 4.58/0.96    inference(resolution,[],[f68,f86])).
% 4.58/0.96  fof(f86,plain,(
% 4.58/0.96    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.58/0.96    inference(cnf_transformation,[],[f29])).
% 4.58/0.96  fof(f29,plain,(
% 4.58/0.96    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(ennf_transformation,[],[f15])).
% 4.58/0.96  fof(f15,axiom,(
% 4.58/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 4.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 4.58/0.96  % (22893)Termination reason: Time limit
% 4.58/0.96  
% 4.58/0.96  % (22893)Memory used [KB]: 8955
% 4.58/0.96  % (22893)Time elapsed: 0.538 s
% 4.58/0.96  % (22893)------------------------------
% 4.58/0.96  % (22893)------------------------------
% 4.58/0.96  fof(f68,plain,(
% 4.58/0.96    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 4.58/0.96    inference(cnf_transformation,[],[f41])).
% 4.58/0.96  fof(f4241,plain,(
% 4.58/0.96    ~r2_hidden(sK4(sK2,sK1),sK0) | spl9_253),
% 4.58/0.96    inference(avatar_component_clause,[],[f4239])).
% 4.58/0.96  fof(f4239,plain,(
% 4.58/0.96    spl9_253 <=> r2_hidden(sK4(sK2,sK1),sK0)),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_253])])).
% 4.58/0.96  fof(f7703,plain,(
% 4.58/0.96    ~spl9_97 | ~spl9_72 | ~spl9_95),
% 4.58/0.96    inference(avatar_split_clause,[],[f7687,f1874,f1281,f1883])).
% 4.58/0.96  fof(f1883,plain,(
% 4.58/0.96    spl9_97 <=> r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK2)),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).
% 4.58/0.96  fof(f1281,plain,(
% 4.58/0.96    spl9_72 <=> r1_xboole_0(sK2,k3_subset_1(sK0,sK2))),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).
% 4.58/0.96  fof(f7687,plain,(
% 4.58/0.96    ~r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK2) | (~spl9_72 | ~spl9_95)),
% 4.58/0.96    inference(resolution,[],[f1607,f1876])).
% 4.58/0.96  fof(f1876,plain,(
% 4.58/0.96    r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2)) | ~spl9_95),
% 4.58/0.96    inference(avatar_component_clause,[],[f1874])).
% 4.58/0.96  fof(f1607,plain,(
% 4.58/0.96    ( ! [X4] : (~r2_hidden(X4,k3_subset_1(sK0,sK2)) | ~r2_hidden(X4,sK2)) ) | ~spl9_72),
% 4.58/0.96    inference(resolution,[],[f1283,f82])).
% 4.58/0.96  fof(f82,plain,(
% 4.58/0.96    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.58/0.96    inference(cnf_transformation,[],[f48])).
% 4.58/0.96  fof(f1283,plain,(
% 4.58/0.96    r1_xboole_0(sK2,k3_subset_1(sK0,sK2)) | ~spl9_72),
% 4.58/0.96    inference(avatar_component_clause,[],[f1281])).
% 4.58/0.96  fof(f4249,plain,(
% 4.58/0.96    spl9_14 | ~spl9_58),
% 4.58/0.96    inference(avatar_split_clause,[],[f3053,f954,f270])).
% 4.58/0.96  fof(f270,plain,(
% 4.58/0.96    spl9_14 <=> r1_xboole_0(sK1,sK2)),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 4.58/0.96  fof(f954,plain,(
% 4.58/0.96    spl9_58 <=> r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).
% 4.58/0.96  fof(f3053,plain,(
% 4.58/0.96    ~r1_tarski(sK2,k3_subset_1(sK0,sK1)) | r1_xboole_0(sK1,sK2)),
% 4.58/0.96    inference(resolution,[],[f631,f68])).
% 4.58/0.96  fof(f631,plain,(
% 4.58/0.96    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(sK0)) | ~r1_tarski(X8,k3_subset_1(sK0,sK1)) | r1_xboole_0(sK1,X8)) )),
% 4.58/0.96    inference(resolution,[],[f136,f84])).
% 4.58/0.96  fof(f84,plain,(
% 4.58/0.96    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 4.58/0.96    inference(cnf_transformation,[],[f27])).
% 4.58/0.96  fof(f27,plain,(
% 4.58/0.96    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 4.58/0.96    inference(ennf_transformation,[],[f5])).
% 4.58/0.96  fof(f5,axiom,(
% 4.58/0.96    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 4.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 4.58/0.96  fof(f136,plain,(
% 4.58/0.96    ( ! [X4] : (r1_xboole_0(X4,sK1) | ~r1_tarski(X4,k3_subset_1(sK0,sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(sK0))) )),
% 4.58/0.96    inference(resolution,[],[f67,f91])).
% 4.58/0.96  fof(f91,plain,(
% 4.58/0.96    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.58/0.96    inference(cnf_transformation,[],[f53])).
% 4.58/0.96  fof(f53,plain,(
% 4.58/0.96    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(nnf_transformation,[],[f32])).
% 4.58/0.96  fof(f32,plain,(
% 4.58/0.96    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(ennf_transformation,[],[f16])).
% 4.58/0.96  fof(f16,axiom,(
% 4.58/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 4.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 4.58/0.96  fof(f4242,plain,(
% 4.58/0.96    spl9_86 | ~spl9_253 | ~spl9_8),
% 4.58/0.96    inference(avatar_split_clause,[],[f3227,f211,f4239,f1587])).
% 4.58/0.96  fof(f211,plain,(
% 4.58/0.96    spl9_8 <=> ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK2))),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 4.58/0.96  fof(f3227,plain,(
% 4.58/0.96    ~r2_hidden(sK4(sK2,sK1),sK0) | r1_xboole_0(sK2,sK1) | ~spl9_8),
% 4.58/0.96    inference(duplicate_literal_removal,[],[f3221])).
% 4.58/0.96  fof(f3221,plain,(
% 4.58/0.96    ~r2_hidden(sK4(sK2,sK1),sK0) | r1_xboole_0(sK2,sK1) | r1_xboole_0(sK2,sK1) | ~spl9_8),
% 4.58/0.96    inference(resolution,[],[f442,f81])).
% 4.58/0.96  fof(f81,plain,(
% 4.58/0.96    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 4.58/0.96    inference(cnf_transformation,[],[f48])).
% 4.58/0.96  fof(f442,plain,(
% 4.58/0.96    ( ! [X10] : (~r2_hidden(sK4(sK2,X10),sK1) | ~r2_hidden(sK4(sK2,X10),sK0) | r1_xboole_0(sK2,X10)) ) | ~spl9_8),
% 4.58/0.96    inference(resolution,[],[f212,f80])).
% 4.58/0.96  fof(f212,plain,(
% 4.58/0.96    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl9_8),
% 4.58/0.96    inference(avatar_component_clause,[],[f211])).
% 4.58/0.96  fof(f4220,plain,(
% 4.58/0.96    spl9_248 | ~spl9_14),
% 4.58/0.96    inference(avatar_split_clause,[],[f3549,f270,f4218])).
% 4.58/0.96  fof(f3549,plain,(
% 4.58/0.96    ( ! [X11] : (~r1_xboole_0(sK1,sK2) | r2_hidden(X11,k3_subset_1(sK0,sK2)) | ~r2_hidden(X11,sK1)) )),
% 4.58/0.96    inference(resolution,[],[f558,f68])).
% 4.58/0.96  fof(f558,plain,(
% 4.58/0.96    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r1_xboole_0(sK1,X3) | r2_hidden(X4,k3_subset_1(sK0,X3)) | ~r2_hidden(X4,sK1)) )),
% 4.58/0.96    inference(resolution,[],[f133,f97])).
% 4.58/0.96  fof(f97,plain,(
% 4.58/0.96    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 4.58/0.96    inference(cnf_transformation,[],[f60])).
% 4.58/0.96  fof(f60,plain,(
% 4.58/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.58/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).
% 4.58/0.96  fof(f59,plain,(
% 4.58/0.96    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 4.58/0.96    introduced(choice_axiom,[])).
% 4.58/0.96  fof(f58,plain,(
% 4.58/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 4.58/0.96    inference(rectify,[],[f57])).
% 4.58/0.96  fof(f57,plain,(
% 4.58/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 4.58/0.96    inference(nnf_transformation,[],[f34])).
% 4.58/0.96  fof(f34,plain,(
% 4.58/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 4.58/0.96    inference(ennf_transformation,[],[f2])).
% 4.58/0.96  fof(f2,axiom,(
% 4.58/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 4.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 4.58/0.96  fof(f133,plain,(
% 4.58/0.96    ( ! [X1] : (r1_tarski(sK1,k3_subset_1(sK0,X1)) | ~r1_xboole_0(sK1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 4.58/0.96    inference(resolution,[],[f67,f90])).
% 4.58/0.96  fof(f90,plain,(
% 4.58/0.96    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.58/0.96    inference(cnf_transformation,[],[f53])).
% 4.58/0.96  fof(f1887,plain,(
% 4.58/0.96    ~spl9_41 | spl9_96 | spl9_95),
% 4.58/0.96    inference(avatar_split_clause,[],[f913,f1874,f1878,f675])).
% 4.58/0.96  fof(f913,plain,(
% 4.58/0.96    r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2)) | r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK1) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 4.58/0.96    inference(resolution,[],[f143,f118])).
% 4.58/0.96  fof(f143,plain,(
% 4.58/0.96    ( ! [X11] : (sQ8_eqProxy(sK1,X11) | r2_hidden(sK5(sK0,sK1,X11),X11) | r2_hidden(sK5(sK0,sK1,X11),sK1) | ~m1_subset_1(X11,k1_zfmisc_1(sK0))) )),
% 4.58/0.96    inference(resolution,[],[f67,f122])).
% 4.58/0.96  fof(f122,plain,(
% 4.58/0.96    ( ! [X2,X0,X1] : (sQ8_eqProxy(X1,X2) | r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.58/0.96    inference(equality_proxy_replacement,[],[f88,f117])).
% 4.58/0.96  fof(f88,plain,(
% 4.58/0.96    ( ! [X2,X0,X1] : (X1 = X2 | r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.58/0.96    inference(cnf_transformation,[],[f52])).
% 4.58/0.96  fof(f1886,plain,(
% 4.58/0.96    ~spl9_12 | ~spl9_41 | spl9_97 | spl9_96),
% 4.58/0.96    inference(avatar_split_clause,[],[f1050,f1878,f1883,f675,f262])).
% 4.58/0.96  fof(f262,plain,(
% 4.58/0.96    spl9_12 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 4.58/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 4.58/0.96  fof(f1050,plain,(
% 4.58/0.96    r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK1) | r2_hidden(sK5(sK0,sK1,k3_subset_1(sK0,sK2)),sK2) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 4.58/0.96    inference(resolution,[],[f224,f118])).
% 4.58/0.96  fof(f224,plain,(
% 4.58/0.96    ( ! [X2,X3] : (sQ8_eqProxy(X2,X3) | r2_hidden(sK5(sK0,X2,X3),sK1) | r2_hidden(sK5(sK0,X2,X3),sK2) | ~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(sK0))) )),
% 4.58/0.96    inference(resolution,[],[f70,f123])).
% 4.58/0.96  fof(f123,plain,(
% 4.58/0.96    ( ! [X2,X0,X1] : (sQ8_eqProxy(X1,X2) | m1_subset_1(sK5(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.58/0.96    inference(equality_proxy_replacement,[],[f87,f117])).
% 4.58/0.96  fof(f87,plain,(
% 4.58/0.96    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK5(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.58/0.96    inference(cnf_transformation,[],[f52])).
% 4.58/0.96  fof(f70,plain,(
% 4.58/0.96    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 4.58/0.96    inference(cnf_transformation,[],[f41])).
% 4.58/0.96  fof(f1872,plain,(
% 4.58/0.96    spl9_41),
% 4.58/0.96    inference(avatar_contradiction_clause,[],[f1868])).
% 4.58/0.96  fof(f1868,plain,(
% 4.58/0.96    $false | spl9_41),
% 4.58/0.96    inference(resolution,[],[f677,f167])).
% 4.58/0.96  fof(f167,plain,(
% 4.58/0.96    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 4.58/0.96    inference(resolution,[],[f68,f85])).
% 4.58/0.96  fof(f85,plain,(
% 4.58/0.96    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.58/0.96    inference(cnf_transformation,[],[f28])).
% 4.58/0.96  fof(f28,plain,(
% 4.58/0.96    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.96    inference(ennf_transformation,[],[f14])).
% 4.58/0.96  fof(f14,axiom,(
% 4.58/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.58/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 4.58/0.97  fof(f677,plain,(
% 4.58/0.97    ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | spl9_41),
% 4.58/0.97    inference(avatar_component_clause,[],[f675])).
% 4.58/0.97  fof(f1591,plain,(
% 4.58/0.97    ~spl9_13 | ~spl9_86 | spl9_58),
% 4.58/0.97    inference(avatar_split_clause,[],[f1581,f954,f1587,f266])).
% 4.58/0.97  fof(f266,plain,(
% 4.58/0.97    spl9_13 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 4.58/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 4.58/0.97  fof(f1581,plain,(
% 4.58/0.97    ~r1_xboole_0(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl9_58),
% 4.58/0.97    inference(resolution,[],[f955,f134])).
% 4.58/0.97  fof(f134,plain,(
% 4.58/0.97    ( ! [X2] : (r1_tarski(X2,k3_subset_1(sK0,sK1)) | ~r1_xboole_0(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(sK0))) )),
% 4.58/0.97    inference(resolution,[],[f67,f90])).
% 4.58/0.97  fof(f955,plain,(
% 4.58/0.97    ~r1_tarski(sK2,k3_subset_1(sK0,sK1)) | spl9_58),
% 4.58/0.97    inference(avatar_component_clause,[],[f954])).
% 4.58/0.97  fof(f1285,plain,(
% 4.58/0.97    ~spl9_13 | spl9_72),
% 4.58/0.97    inference(avatar_split_clause,[],[f869,f1281,f266])).
% 4.58/0.97  fof(f869,plain,(
% 4.58/0.97    r1_xboole_0(sK2,k3_subset_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 4.58/0.97    inference(resolution,[],[f176,f113])).
% 4.58/0.97  fof(f113,plain,(
% 4.58/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.58/0.97    inference(equality_resolution,[],[f94])).
% 4.58/0.97  fof(f94,plain,(
% 4.58/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.58/0.97    inference(cnf_transformation,[],[f56])).
% 4.58/0.97  fof(f56,plain,(
% 4.58/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.58/0.97    inference(flattening,[],[f55])).
% 4.58/0.97  fof(f55,plain,(
% 4.58/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.58/0.97    inference(nnf_transformation,[],[f7])).
% 4.58/0.97  fof(f7,axiom,(
% 4.58/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.58/0.97  fof(f176,plain,(
% 4.58/0.97    ( ! [X8] : (~r1_tarski(X8,sK2) | r1_xboole_0(X8,k3_subset_1(sK0,sK2)) | ~m1_subset_1(X8,k1_zfmisc_1(sK0))) )),
% 4.58/0.97    inference(resolution,[],[f68,f93])).
% 4.58/0.97  fof(f93,plain,(
% 4.58/0.97    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.58/0.97    inference(cnf_transformation,[],[f54])).
% 4.58/0.97  fof(f54,plain,(
% 4.58/0.97    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.97    inference(nnf_transformation,[],[f33])).
% 4.58/0.97  fof(f33,plain,(
% 4.58/0.97    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.58/0.97    inference(ennf_transformation,[],[f17])).
% 4.58/0.97  fof(f17,axiom,(
% 4.58/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 4.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 4.58/0.97  fof(f1268,plain,(
% 4.58/0.97    spl9_13),
% 4.58/0.97    inference(avatar_contradiction_clause,[],[f1265])).
% 4.58/0.97  fof(f1265,plain,(
% 4.58/0.97    $false | spl9_13),
% 4.58/0.97    inference(resolution,[],[f268,f68])).
% 4.58/0.97  fof(f268,plain,(
% 4.58/0.97    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl9_13),
% 4.58/0.97    inference(avatar_component_clause,[],[f266])).
% 4.58/0.97  fof(f1258,plain,(
% 4.58/0.97    spl9_12),
% 4.58/0.97    inference(avatar_contradiction_clause,[],[f1255])).
% 4.58/0.97  fof(f1255,plain,(
% 4.58/0.97    $false | spl9_12),
% 4.58/0.97    inference(resolution,[],[f264,f67])).
% 4.58/0.97  fof(f264,plain,(
% 4.58/0.97    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl9_12),
% 4.58/0.97    inference(avatar_component_clause,[],[f262])).
% 4.58/0.97  fof(f932,plain,(
% 4.58/0.97    spl9_14 | ~spl9_23),
% 4.58/0.97    inference(avatar_contradiction_clause,[],[f929])).
% 4.58/0.97  fof(f929,plain,(
% 4.58/0.97    $false | (spl9_14 | ~spl9_23)),
% 4.58/0.97    inference(resolution,[],[f570,f272])).
% 4.58/0.97  fof(f272,plain,(
% 4.58/0.97    ~r1_xboole_0(sK1,sK2) | spl9_14),
% 4.58/0.97    inference(avatar_component_clause,[],[f270])).
% 4.58/0.97  fof(f570,plain,(
% 4.58/0.97    ( ! [X10] : (r1_xboole_0(X10,sK2)) ) | ~spl9_23),
% 4.58/0.97    inference(resolution,[],[f480,f81])).
% 4.58/0.97  fof(f480,plain,(
% 4.58/0.97    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl9_23),
% 4.58/0.97    inference(avatar_component_clause,[],[f479])).
% 4.58/0.97  fof(f479,plain,(
% 4.58/0.97    spl9_23 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 4.58/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 4.58/0.97  fof(f481,plain,(
% 4.58/0.97    ~spl9_7 | spl9_23),
% 4.58/0.97    inference(avatar_split_clause,[],[f400,f479,f207])).
% 4.58/0.97  fof(f207,plain,(
% 4.58/0.97    spl9_7 <=> v1_xboole_0(sK0)),
% 4.58/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 4.58/0.97  fof(f400,plain,(
% 4.58/0.97    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_xboole_0(sK0)) )),
% 4.58/0.97    inference(resolution,[],[f168,f72])).
% 4.58/0.97  fof(f72,plain,(
% 4.58/0.97    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 4.58/0.97    inference(cnf_transformation,[],[f45])).
% 4.58/0.97  fof(f45,plain,(
% 4.58/0.97    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.58/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 4.58/0.97  fof(f44,plain,(
% 4.58/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 4.58/0.97    introduced(choice_axiom,[])).
% 4.58/0.97  fof(f43,plain,(
% 4.58/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.58/0.97    inference(rectify,[],[f42])).
% 4.58/0.97  fof(f42,plain,(
% 4.58/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 4.58/0.97    inference(nnf_transformation,[],[f1])).
% 4.58/0.97  fof(f1,axiom,(
% 4.58/0.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 4.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 4.58/0.97  fof(f213,plain,(
% 4.58/0.97    spl9_7 | spl9_8),
% 4.58/0.97    inference(avatar_split_clause,[],[f203,f211,f207])).
% 4.58/0.97  fof(f203,plain,(
% 4.58/0.97    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 4.58/0.97    inference(resolution,[],[f69,f77])).
% 4.58/0.97  fof(f77,plain,(
% 4.58/0.97    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 4.58/0.97    inference(cnf_transformation,[],[f46])).
% 4.58/0.97  fof(f46,plain,(
% 4.58/0.97    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 4.58/0.97    inference(nnf_transformation,[],[f24])).
% 4.58/0.97  fof(f24,plain,(
% 4.58/0.97    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 4.58/0.97    inference(ennf_transformation,[],[f13])).
% 4.58/0.97  fof(f13,axiom,(
% 4.58/0.97    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 4.58/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 4.58/0.97  fof(f69,plain,(
% 4.58/0.97    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) )),
% 4.58/0.97    inference(cnf_transformation,[],[f41])).
% 4.58/0.97  % SZS output end Proof for theBenchmark
% 4.58/0.97  % (22896)------------------------------
% 4.58/0.97  % (22896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/0.97  % (22896)Termination reason: Refutation
% 4.58/0.97  
% 4.58/0.97  % (22896)Memory used [KB]: 10618
% 4.58/0.97  % (22896)Time elapsed: 0.539 s
% 4.58/0.97  % (22896)------------------------------
% 4.58/0.97  % (22896)------------------------------
% 4.58/0.97  % (22880)Success in time 0.609 s
%------------------------------------------------------------------------------
