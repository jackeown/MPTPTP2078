%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0343+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:47 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 143 expanded)
%              Number of leaves         :   13 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  273 ( 757 expanded)
%              Number of equality atoms :   20 (  62 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f58,f70,f80,f108,f140])).

fof(f140,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | spl4_6
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f138,f65])).

fof(f65,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_6
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f138,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f43,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f137,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f134,f38])).

fof(f38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f134,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1)
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f69,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK3(X0,X1,X2),X2)
            & r2_hidden(sK3(X0,X1,X2),X1)
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f69,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,sK2,sK1),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_7
  <=> ! [X0] :
        ( ~ m1_subset_1(sK3(X0,sK2,sK1),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f108,plain,
    ( spl4_4
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f105,f56,f41,f36,f52])).

fof(f52,plain,
    ( spl4_4
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f56,plain,
    ( spl4_5
  <=> ! [X0] :
        ( ~ m1_subset_1(sK3(X0,sK1,sK2),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f105,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f104,f38])).

fof(f104,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f101,f43])).

fof(f101,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ spl4_5 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_5 ),
    inference(resolution,[],[f57,f25])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,sK1,sK2),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f80,plain,
    ( ~ spl4_4
    | spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f79,f64,f31,f52])).

fof(f31,plain,
    ( spl4_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f79,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f74,f33])).

fof(f33,plain,
    ( sK1 != sK2
    | spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f74,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = sK2
    | ~ spl4_6 ),
    inference(resolution,[],[f66,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f66,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f70,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f62,f68,f64])).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(X0,sK2,sK1),sK0)
      | r1_tarski(sK2,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(X0,sK2,sK1),sK0)
      | r1_tarski(sK2,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r1_tarski(sK2,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f46,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,sK1),sK2)
      | ~ m1_subset_1(sK3(X0,X1,sK1),sK0)
      | r1_tarski(X1,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X2] :
        ( sK1 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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

fof(f58,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f50,f56,f52])).

fof(f50,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(X0,sK1,sK2),sK0)
      | r1_tarski(sK1,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(X0,sK1,sK2),sK0)
      | r1_tarski(sK1,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | r1_tarski(sK1,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f45,f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,sK2),sK1)
      | ~ m1_subset_1(sK3(X0,X1,sK2),sK0)
      | r1_tarski(X1,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f19,f27])).

fof(f19,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f31])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
