%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0414+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  91 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  132 ( 297 expanded)
%              Number of equality atoms :    9 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f54,f74,f81])).

fof(f81,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f80,f36,f46])).

fof(f46,plain,
    ( spl4_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f36,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f80,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,
    ( r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f69,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f69,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK2,X0),sK1)
        | r1_tarski(sK2,X0) )
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,X0)
        | r2_hidden(sK3(sK2,X0),sK1)
        | r1_tarski(sK2,X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f64,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK2,X1),sK2)
        | r1_tarski(sK2,X1)
        | r2_hidden(sK3(sK2,X1),sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f59,f11])).

fof(f11,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f59,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3(sK2,X1),k1_zfmisc_1(sK0))
        | r1_tarski(sK2,X1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f56,f38])).

fof(f38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK3(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f22,f20])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f74,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f73,f26,f50])).

fof(f50,plain,
    ( spl4_5
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f26,plain,
    ( spl4_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f73,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f67,f21])).

fof(f67,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,X0),sK2)
        | r1_tarski(sK1,X0) )
    | ~ spl4_1 ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,X0),sK2)
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f60,f20])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,X0),sK1)
        | r2_hidden(sK3(sK1,X0),sK2)
        | r1_tarski(sK1,X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f58,f12])).

fof(f12,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK1,X0),k1_zfmisc_1(sK0))
        | r1_tarski(sK1,X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f56,f28])).

fof(f28,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f54,plain,
    ( ~ spl4_5
    | ~ spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f43,f31,f46,f50])).

fof(f31,plain,
    ( spl4_2
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f43,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK1,sK2)
    | spl4_2 ),
    inference(extensionality_resolution,[],[f18,f33])).

fof(f33,plain,
    ( sK1 != sK2
    | spl4_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f39,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f13,f36])).

fof(f13,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
