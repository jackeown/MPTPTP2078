%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:52 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 307 expanded)
%              Number of leaves         :   33 ( 133 expanded)
%              Depth                    :   15
%              Number of atoms          :  752 (1334 expanded)
%              Number of equality atoms :   59 ( 132 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f91,f97,f102,f108,f116,f123,f136,f154,f194,f208,f214,f265,f299,f312,f329,f348])).

fof(f348,plain,
    ( spl4_6
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | spl4_6
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f341,f96])).

fof(f96,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_6
  <=> k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f341,plain,
    ( k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))
    | ~ spl4_36 ),
    inference(resolution,[],[f328,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f328,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl4_36
  <=> ! [X0] : ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f329,plain,
    ( spl4_36
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_19
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f323,f310,f212,f105,f88,f327])).

fof(f88,plain,
    ( spl4_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f105,plain,
    ( spl4_8
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f212,plain,
    ( spl4_19
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f310,plain,
    ( spl4_34
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f323,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_19
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f322,f213])).

fof(f213,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f212])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) )
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f321,f107])).

fof(f107,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),u1_struct_0(sK0)) )
    | ~ spl4_5
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f320,f90])).

fof(f90,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl4_34 ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl4_34 ),
    inference(resolution,[],[f311,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

% (24807)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f311,plain,
    ( ! [X0,X1] :
        ( r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f310])).

fof(f312,plain,
    ( spl4_34
    | spl4_9
    | ~ spl4_19
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f307,f297,f212,f113,f310])).

fof(f113,plain,
    ( spl4_9
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f297,plain,
    ( spl4_32
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f307,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0))) )
    | spl4_9
    | ~ spl4_19
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f306,f213])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) )
    | spl4_9
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f304,f115])).

fof(f115,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f304,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0)))
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) )
    | ~ spl4_32 ),
    inference(resolution,[],[f298,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f298,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0))) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f297])).

fof(f299,plain,
    ( spl4_32
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f271,f263,f151,f120,f297])).

fof(f120,plain,
    ( spl4_10
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f151,plain,
    ( spl4_12
  <=> k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f263,plain,
    ( spl4_27
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),sK3(X0,sK0,k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f271,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0))) )
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f270,f153])).

fof(f153,plain,
    ( k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0))) )
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(resolution,[],[f264,f122])).

fof(f122,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f264,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),sK3(X0,sK0,k2_struct_0(sK0))) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( spl4_27
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f219,f212,f192,f263])).

fof(f192,plain,
    ( spl4_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f219,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),sK3(X0,sK0,k2_struct_0(sK0))) )
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(resolution,[],[f213,f193])).

fof(f193,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f192])).

fof(f214,plain,
    ( spl4_19
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f210,f206,f151,f120,f212])).

fof(f206,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) )
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f209,f153])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) )
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(resolution,[],[f207,f122])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f206])).

fof(f208,plain,
    ( spl4_18
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f149,f105,f88,f83,f78,f73,f68,f206])).

fof(f68,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f73,plain,
    ( spl4_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f78,plain,
    ( spl4_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f83,plain,
    ( spl4_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f148,f70])).

fof(f70,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f147,f75])).

fof(f75,plain,
    ( v3_orders_2(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f146,f80])).

fof(f80,plain,
    ( v4_orders_2(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f145,f85])).

fof(f85,plain,
    ( v5_orders_2(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f144,f90])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_8 ),
    inference(superposition,[],[f56,f107])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
                & r2_hidden(sK2(X1,X2,X3),X2)
                & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).

fof(f35,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f194,plain,
    ( spl4_17
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f173,f105,f88,f83,f78,f73,f68,f192])).

fof(f173,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f172,f107])).

fof(f172,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f171,f107])).

fof(f171,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f170,f70])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f169,f75])).

fof(f169,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f168,f80])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f167,f90])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f58,f85])).

fof(f58,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r2_orders_2(X1,sK3(X0,X1,X2),X6)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f154,plain,
    ( spl4_12
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f143,f134,f120,f151])).

fof(f134,plain,
    ( spl4_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f143,plain,
    ( k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(resolution,[],[f135,f122])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,
    ( spl4_11
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f132,f105,f88,f83,f78,f73,f68,f134])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f131,f107])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f130,f70])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f129,f75])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f128,f80])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f127,f90])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f50,f85])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f123,plain,
    ( spl4_10
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f118,f105,f99,f120])).

fof(f99,plain,
    ( spl4_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f118,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f117,f101])).

fof(f101,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f117,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl4_8 ),
    inference(superposition,[],[f45,f107])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f116,plain,
    ( ~ spl4_9
    | spl4_1
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f111,f105,f99,f68,f113])).

fof(f111,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl4_1
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f110,f70])).

fof(f110,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f109,f101])).

fof(f109,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_8 ),
    inference(superposition,[],[f51,f107])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f108,plain,
    ( spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f103,f99,f105])).

fof(f103,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f44,f101])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f102,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f92,f88,f99])).

fof(f92,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f46,f90])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f97,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f91,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f42,f88])).

fof(f42,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f41,f83])).

fof(f41,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f39,f73])).

fof(f39,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

% (24813)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:26:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (24799)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (24812)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (24809)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (24789)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (24788)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.25/0.51  % (24805)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.25/0.51  % (24790)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.25/0.51  % (24801)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.25/0.51  % (24794)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.25/0.52  % (24791)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.25/0.52  % (24792)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.25/0.52  % (24804)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.25/0.52  % (24794)Refutation not found, incomplete strategy% (24794)------------------------------
% 1.25/0.52  % (24794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (24794)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (24794)Memory used [KB]: 10618
% 1.25/0.52  % (24794)Time elapsed: 0.103 s
% 1.25/0.52  % (24794)------------------------------
% 1.25/0.52  % (24794)------------------------------
% 1.25/0.52  % (24798)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.25/0.52  % (24790)Refutation found. Thanks to Tanya!
% 1.25/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.52  % (24788)Refutation not found, incomplete strategy% (24788)------------------------------
% 1.25/0.52  % (24788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (24788)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (24788)Memory used [KB]: 10618
% 1.25/0.52  % (24788)Time elapsed: 0.101 s
% 1.25/0.52  % (24788)------------------------------
% 1.25/0.52  % (24788)------------------------------
% 1.25/0.52  % (24802)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.25/0.52  % (24803)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.25/0.53  % (24795)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.25/0.53  % (24797)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.25/0.53  % (24806)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.25/0.53  % (24796)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.25/0.53  % (24799)Refutation not found, incomplete strategy% (24799)------------------------------
% 1.25/0.53  % (24799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (24810)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.37/0.53  % (24800)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.37/0.54  % (24799)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (24799)Memory used [KB]: 10746
% 1.37/0.54  % (24799)Time elapsed: 0.116 s
% 1.37/0.54  % (24799)------------------------------
% 1.37/0.54  % (24799)------------------------------
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  fof(f349,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(avatar_sat_refutation,[],[f71,f76,f81,f86,f91,f97,f102,f108,f116,f123,f136,f154,f194,f208,f214,f265,f299,f312,f329,f348])).
% 1.37/0.54  fof(f348,plain,(
% 1.37/0.54    spl4_6 | ~spl4_36),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f347])).
% 1.37/0.54  fof(f347,plain,(
% 1.37/0.54    $false | (spl4_6 | ~spl4_36)),
% 1.37/0.54    inference(subsumption_resolution,[],[f341,f96])).
% 1.37/0.54  fof(f96,plain,(
% 1.37/0.54    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) | spl4_6),
% 1.37/0.54    inference(avatar_component_clause,[],[f94])).
% 1.37/0.54  fof(f94,plain,(
% 1.37/0.54    spl4_6 <=> k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.37/0.54  fof(f341,plain,(
% 1.37/0.54    k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) | ~spl4_36),
% 1.37/0.54    inference(resolution,[],[f328,f52])).
% 1.37/0.54  fof(f52,plain,(
% 1.37/0.54    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.37/0.54    inference(cnf_transformation,[],[f32])).
% 1.37/0.54  fof(f32,plain,(
% 1.37/0.54    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).
% 1.37/0.54  fof(f31,plain,(
% 1.37/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f22,plain,(
% 1.37/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.37/0.54    inference(ennf_transformation,[],[f2])).
% 1.37/0.54  fof(f2,axiom,(
% 1.37/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.37/0.54  fof(f328,plain,(
% 1.37/0.54    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))) ) | ~spl4_36),
% 1.37/0.54    inference(avatar_component_clause,[],[f327])).
% 1.37/0.54  fof(f327,plain,(
% 1.37/0.54    spl4_36 <=> ! [X0] : ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.37/0.54  fof(f329,plain,(
% 1.37/0.54    spl4_36 | ~spl4_5 | ~spl4_8 | ~spl4_19 | ~spl4_34),
% 1.37/0.54    inference(avatar_split_clause,[],[f323,f310,f212,f105,f88,f327])).
% 1.37/0.54  fof(f88,plain,(
% 1.37/0.54    spl4_5 <=> l1_orders_2(sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.37/0.54  fof(f105,plain,(
% 1.37/0.54    spl4_8 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.37/0.54  fof(f212,plain,(
% 1.37/0.54    spl4_19 <=> ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.37/0.54  fof(f310,plain,(
% 1.37/0.54    spl4_34 <=> ! [X1,X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0))))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.37/0.54  fof(f323,plain,(
% 1.37/0.54    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))) ) | (~spl4_5 | ~spl4_8 | ~spl4_19 | ~spl4_34)),
% 1.37/0.54    inference(subsumption_resolution,[],[f322,f213])).
% 1.37/0.54  fof(f213,plain,(
% 1.37/0.54    ( ! [X0] : (m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))) ) | ~spl4_19),
% 1.37/0.54    inference(avatar_component_clause,[],[f212])).
% 1.37/0.54  fof(f322,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))) ) | (~spl4_5 | ~spl4_8 | ~spl4_34)),
% 1.37/0.54    inference(forward_demodulation,[],[f321,f107])).
% 1.37/0.54  fof(f107,plain,(
% 1.37/0.54    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl4_8),
% 1.37/0.54    inference(avatar_component_clause,[],[f105])).
% 1.37/0.54  fof(f321,plain,(
% 1.37/0.54    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),u1_struct_0(sK0))) ) | (~spl4_5 | ~spl4_34)),
% 1.37/0.54    inference(subsumption_resolution,[],[f320,f90])).
% 1.37/0.54  fof(f90,plain,(
% 1.37/0.54    l1_orders_2(sK0) | ~spl4_5),
% 1.37/0.54    inference(avatar_component_clause,[],[f88])).
% 1.37/0.54  fof(f320,plain,(
% 1.37/0.54    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl4_34),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f317])).
% 1.37/0.54  fof(f317,plain,(
% 1.37/0.54    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl4_34),
% 1.37/0.54    inference(resolution,[],[f311,f66])).
% 1.37/0.54  fof(f66,plain,(
% 1.37/0.54    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f62])).
% 1.37/0.54  fof(f62,plain,(
% 1.37/0.54    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.37/0.54    inference(equality_resolution,[],[f48])).
% 1.37/0.54  fof(f48,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f30])).
% 1.37/0.54  fof(f30,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.37/0.54    inference(flattening,[],[f29])).
% 1.37/0.54  fof(f29,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.37/0.54    inference(nnf_transformation,[],[f17])).
% 1.37/0.54  % (24807)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.37/0.54  fof(f17,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f6])).
% 1.37/0.54  fof(f6,axiom,(
% 1.37/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 1.37/0.54  fof(f311,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0))) | ~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))) ) | ~spl4_34),
% 1.37/0.54    inference(avatar_component_clause,[],[f310])).
% 1.37/0.54  fof(f312,plain,(
% 1.37/0.54    spl4_34 | spl4_9 | ~spl4_19 | ~spl4_32),
% 1.37/0.54    inference(avatar_split_clause,[],[f307,f297,f212,f113,f310])).
% 1.37/0.54  fof(f113,plain,(
% 1.37/0.54    spl4_9 <=> v1_xboole_0(k2_struct_0(sK0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.37/0.54  fof(f297,plain,(
% 1.37/0.54    spl4_32 <=> ! [X1,X0] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0))))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.37/0.54  fof(f307,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0)))) ) | (spl4_9 | ~spl4_19 | ~spl4_32)),
% 1.37/0.54    inference(subsumption_resolution,[],[f306,f213])).
% 1.37/0.54  fof(f306,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0))) | ~m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))) ) | (spl4_9 | ~spl4_32)),
% 1.37/0.54    inference(subsumption_resolution,[],[f304,f115])).
% 1.37/0.54  fof(f115,plain,(
% 1.37/0.54    ~v1_xboole_0(k2_struct_0(sK0)) | spl4_9),
% 1.37/0.54    inference(avatar_component_clause,[],[f113])).
% 1.37/0.54  fof(f304,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))) ) | ~spl4_32),
% 1.37/0.54    inference(resolution,[],[f298,f55])).
% 1.37/0.54  fof(f55,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f24])).
% 1.37/0.54  fof(f24,plain,(
% 1.37/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.37/0.54    inference(flattening,[],[f23])).
% 1.37/0.54  fof(f23,plain,(
% 1.37/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f1])).
% 1.37/0.54  fof(f1,axiom,(
% 1.37/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.37/0.54  fof(f298,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0)))) ) | ~spl4_32),
% 1.37/0.54    inference(avatar_component_clause,[],[f297])).
% 1.37/0.54  fof(f299,plain,(
% 1.37/0.54    spl4_32 | ~spl4_10 | ~spl4_12 | ~spl4_27),
% 1.37/0.54    inference(avatar_split_clause,[],[f271,f263,f151,f120,f297])).
% 1.37/0.54  fof(f120,plain,(
% 1.37/0.54    spl4_10 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.37/0.54  fof(f151,plain,(
% 1.37/0.54    spl4_12 <=> k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.37/0.54  fof(f263,plain,(
% 1.37/0.54    spl4_27 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | r2_orders_2(sK0,sK3(X2,sK0,X1),sK3(X0,sK0,k2_struct_0(sK0))))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.37/0.54  fof(f271,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0)))) ) | (~spl4_10 | ~spl4_12 | ~spl4_27)),
% 1.37/0.54    inference(forward_demodulation,[],[f270,f153])).
% 1.37/0.54  fof(f153,plain,(
% 1.37/0.54    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) | ~spl4_12),
% 1.37/0.54    inference(avatar_component_clause,[],[f151])).
% 1.37/0.54  fof(f270,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~r2_hidden(X1,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK3(X1,sK0,k2_struct_0(sK0)),sK3(X0,sK0,k2_struct_0(sK0)))) ) | (~spl4_10 | ~spl4_27)),
% 1.37/0.54    inference(resolution,[],[f264,f122])).
% 1.37/0.54  fof(f122,plain,(
% 1.37/0.54    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_10),
% 1.37/0.54    inference(avatar_component_clause,[],[f120])).
% 1.37/0.54  fof(f264,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | r2_orders_2(sK0,sK3(X2,sK0,X1),sK3(X0,sK0,k2_struct_0(sK0)))) ) | ~spl4_27),
% 1.37/0.54    inference(avatar_component_clause,[],[f263])).
% 1.37/0.54  fof(f265,plain,(
% 1.37/0.54    spl4_27 | ~spl4_17 | ~spl4_19),
% 1.37/0.54    inference(avatar_split_clause,[],[f219,f212,f192,f263])).
% 1.37/0.54  fof(f192,plain,(
% 1.37/0.54    spl4_17 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.37/0.54  fof(f219,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK3(X0,sK0,k2_struct_0(sK0)),X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | r2_orders_2(sK0,sK3(X2,sK0,X1),sK3(X0,sK0,k2_struct_0(sK0)))) ) | (~spl4_17 | ~spl4_19)),
% 1.37/0.54    inference(resolution,[],[f213,f193])).
% 1.37/0.54  fof(f193,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)) ) | ~spl4_17),
% 1.37/0.54    inference(avatar_component_clause,[],[f192])).
% 1.37/0.54  fof(f214,plain,(
% 1.37/0.54    spl4_19 | ~spl4_10 | ~spl4_12 | ~spl4_18),
% 1.37/0.54    inference(avatar_split_clause,[],[f210,f206,f151,f120,f212])).
% 1.37/0.54  fof(f206,plain,(
% 1.37/0.54    spl4_18 <=> ! [X1,X0] : (m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.37/0.54  fof(f210,plain,(
% 1.37/0.54    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))) ) | (~spl4_10 | ~spl4_12 | ~spl4_18)),
% 1.37/0.54    inference(forward_demodulation,[],[f209,f153])).
% 1.37/0.54  fof(f209,plain,(
% 1.37/0.54    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))) ) | (~spl4_10 | ~spl4_18)),
% 1.37/0.54    inference(resolution,[],[f207,f122])).
% 1.37/0.54  fof(f207,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0))) ) | ~spl4_18),
% 1.37/0.54    inference(avatar_component_clause,[],[f206])).
% 1.37/0.54  fof(f208,plain,(
% 1.37/0.54    spl4_18 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8),
% 1.37/0.54    inference(avatar_split_clause,[],[f149,f105,f88,f83,f78,f73,f68,f206])).
% 1.37/0.54  fof(f68,plain,(
% 1.37/0.54    spl4_1 <=> v2_struct_0(sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.37/0.54  fof(f73,plain,(
% 1.37/0.54    spl4_2 <=> v3_orders_2(sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.37/0.54  fof(f78,plain,(
% 1.37/0.54    spl4_3 <=> v4_orders_2(sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.37/0.54  fof(f83,plain,(
% 1.37/0.54    spl4_4 <=> v5_orders_2(sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.37/0.54  fof(f149,plain,(
% 1.37/0.54    ( ! [X0,X1] : (m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8)),
% 1.37/0.54    inference(subsumption_resolution,[],[f148,f70])).
% 1.37/0.54  fof(f70,plain,(
% 1.37/0.54    ~v2_struct_0(sK0) | spl4_1),
% 1.37/0.54    inference(avatar_component_clause,[],[f68])).
% 1.37/0.54  fof(f148,plain,(
% 1.37/0.54    ( ! [X0,X1] : (m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8)),
% 1.37/0.54    inference(subsumption_resolution,[],[f147,f75])).
% 1.37/0.54  fof(f75,plain,(
% 1.37/0.54    v3_orders_2(sK0) | ~spl4_2),
% 1.37/0.54    inference(avatar_component_clause,[],[f73])).
% 1.37/0.54  fof(f147,plain,(
% 1.37/0.54    ( ! [X0,X1] : (m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8)),
% 1.37/0.54    inference(subsumption_resolution,[],[f146,f80])).
% 1.37/0.54  fof(f80,plain,(
% 1.37/0.54    v4_orders_2(sK0) | ~spl4_3),
% 1.37/0.54    inference(avatar_component_clause,[],[f78])).
% 1.37/0.54  fof(f146,plain,(
% 1.37/0.54    ( ! [X0,X1] : (m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5 | ~spl4_8)),
% 1.37/0.54    inference(subsumption_resolution,[],[f145,f85])).
% 1.37/0.54  fof(f85,plain,(
% 1.37/0.54    v5_orders_2(sK0) | ~spl4_4),
% 1.37/0.54    inference(avatar_component_clause,[],[f83])).
% 1.37/0.54  fof(f145,plain,(
% 1.37/0.54    ( ! [X0,X1] : (m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | ~spl4_8)),
% 1.37/0.54    inference(subsumption_resolution,[],[f144,f90])).
% 1.37/0.54  fof(f144,plain,(
% 1.37/0.54    ( ! [X0,X1] : (m1_subset_1(sK3(X0,sK0,X1),k2_struct_0(sK0)) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_8),
% 1.37/0.54    inference(superposition,[],[f56,f107])).
% 1.37/0.54  fof(f56,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f37])).
% 1.37/0.54  fof(f37,plain,(
% 1.37/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f36,plain,(
% 1.37/0.54    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f34,plain,(
% 1.37/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.37/0.54    inference(rectify,[],[f33])).
% 1.37/0.54  fof(f33,plain,(
% 1.37/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.37/0.54    inference(nnf_transformation,[],[f26])).
% 1.37/0.54  fof(f26,plain,(
% 1.37/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.37/0.54    inference(flattening,[],[f25])).
% 1.37/0.54  fof(f25,plain,(
% 1.37/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.37/0.54    inference(ennf_transformation,[],[f9])).
% 1.37/0.54  fof(f9,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 1.37/0.54  fof(f194,plain,(
% 1.37/0.54    spl4_17 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8),
% 1.37/0.54    inference(avatar_split_clause,[],[f173,f105,f88,f83,f78,f73,f68,f192])).
% 1.37/0.54  fof(f173,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8)),
% 1.37/0.54    inference(forward_demodulation,[],[f172,f107])).
% 1.37/0.54  fof(f172,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8)),
% 1.37/0.54    inference(forward_demodulation,[],[f171,f107])).
% 1.37/0.54  fof(f171,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.37/0.54    inference(subsumption_resolution,[],[f170,f70])).
% 1.37/0.54  fof(f170,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.37/0.54    inference(subsumption_resolution,[],[f169,f75])).
% 1.37/0.54  fof(f169,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.37/0.54    inference(subsumption_resolution,[],[f168,f80])).
% 1.37/0.54  fof(f168,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5)),
% 1.37/0.54    inference(subsumption_resolution,[],[f167,f90])).
% 1.37/0.54  fof(f167,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | r2_orders_2(sK0,sK3(X2,sK0,X1),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_4),
% 1.37/0.54    inference(resolution,[],[f58,f85])).
% 1.37/0.54  fof(f58,plain,(
% 1.37/0.54    ( ! [X6,X2,X0,X1] : (~v5_orders_2(X1) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f37])).
% 1.37/0.54  fof(f154,plain,(
% 1.37/0.54    spl4_12 | ~spl4_10 | ~spl4_11),
% 1.37/0.54    inference(avatar_split_clause,[],[f143,f134,f120,f151])).
% 1.37/0.54  fof(f134,plain,(
% 1.37/0.54    spl4_11 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0))),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.37/0.54  fof(f143,plain,(
% 1.37/0.54    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) | (~spl4_10 | ~spl4_11)),
% 1.37/0.54    inference(resolution,[],[f135,f122])).
% 1.37/0.54  fof(f135,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) ) | ~spl4_11),
% 1.37/0.54    inference(avatar_component_clause,[],[f134])).
% 1.37/0.54  fof(f136,plain,(
% 1.37/0.54    spl4_11 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8),
% 1.37/0.54    inference(avatar_split_clause,[],[f132,f105,f88,f83,f78,f73,f68,f134])).
% 1.37/0.54  fof(f132,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_8)),
% 1.37/0.54    inference(forward_demodulation,[],[f131,f107])).
% 1.37/0.54  fof(f131,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.37/0.54    inference(subsumption_resolution,[],[f130,f70])).
% 1.37/0.54  fof(f130,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.37/0.54    inference(subsumption_resolution,[],[f129,f75])).
% 1.37/0.54  fof(f129,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.37/0.54    inference(subsumption_resolution,[],[f128,f80])).
% 1.37/0.54  fof(f128,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5)),
% 1.37/0.54    inference(subsumption_resolution,[],[f127,f90])).
% 1.37/0.54  fof(f127,plain,(
% 1.37/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_4),
% 1.37/0.54    inference(resolution,[],[f50,f85])).
% 1.37/0.54  fof(f50,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f19])).
% 1.37/0.54  fof(f19,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.37/0.54    inference(flattening,[],[f18])).
% 1.37/0.54  fof(f18,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f7])).
% 1.37/0.54  fof(f7,axiom,(
% 1.37/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 1.37/0.54  fof(f123,plain,(
% 1.37/0.54    spl4_10 | ~spl4_7 | ~spl4_8),
% 1.37/0.54    inference(avatar_split_clause,[],[f118,f105,f99,f120])).
% 1.37/0.54  fof(f99,plain,(
% 1.37/0.54    spl4_7 <=> l1_struct_0(sK0)),
% 1.37/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.37/0.54  fof(f118,plain,(
% 1.37/0.54    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_7 | ~spl4_8)),
% 1.37/0.54    inference(subsumption_resolution,[],[f117,f101])).
% 1.37/0.54  fof(f101,plain,(
% 1.37/0.54    l1_struct_0(sK0) | ~spl4_7),
% 1.37/0.54    inference(avatar_component_clause,[],[f99])).
% 1.37/0.54  fof(f117,plain,(
% 1.37/0.54    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_struct_0(sK0) | ~spl4_8),
% 1.37/0.54    inference(superposition,[],[f45,f107])).
% 1.37/0.54  fof(f45,plain,(
% 1.37/0.54    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f15])).
% 1.37/0.54  fof(f15,plain,(
% 1.37/0.54    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f4])).
% 1.37/0.54  fof(f4,axiom,(
% 1.37/0.54    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 1.37/0.54  fof(f116,plain,(
% 1.37/0.54    ~spl4_9 | spl4_1 | ~spl4_7 | ~spl4_8),
% 1.37/0.54    inference(avatar_split_clause,[],[f111,f105,f99,f68,f113])).
% 1.37/0.54  fof(f111,plain,(
% 1.37/0.54    ~v1_xboole_0(k2_struct_0(sK0)) | (spl4_1 | ~spl4_7 | ~spl4_8)),
% 1.37/0.54    inference(subsumption_resolution,[],[f110,f70])).
% 1.37/0.54  fof(f110,plain,(
% 1.37/0.54    ~v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | (~spl4_7 | ~spl4_8)),
% 1.37/0.54    inference(subsumption_resolution,[],[f109,f101])).
% 1.37/0.54  fof(f109,plain,(
% 1.37/0.54    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_8),
% 1.37/0.54    inference(superposition,[],[f51,f107])).
% 1.37/0.54  fof(f51,plain,(
% 1.37/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f21])).
% 1.37/0.54  fof(f21,plain,(
% 1.37/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.37/0.54    inference(flattening,[],[f20])).
% 1.37/0.54  fof(f20,plain,(
% 1.37/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f5])).
% 1.37/0.54  fof(f5,axiom,(
% 1.37/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.37/0.54  fof(f108,plain,(
% 1.37/0.54    spl4_8 | ~spl4_7),
% 1.37/0.54    inference(avatar_split_clause,[],[f103,f99,f105])).
% 1.37/0.54  fof(f103,plain,(
% 1.37/0.54    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl4_7),
% 1.37/0.54    inference(resolution,[],[f44,f101])).
% 1.37/0.54  fof(f44,plain,(
% 1.37/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f14])).
% 1.37/0.54  fof(f14,plain,(
% 1.37/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.37/0.54  fof(f102,plain,(
% 1.37/0.54    spl4_7 | ~spl4_5),
% 1.37/0.54    inference(avatar_split_clause,[],[f92,f88,f99])).
% 1.37/0.54  fof(f92,plain,(
% 1.37/0.54    l1_struct_0(sK0) | ~spl4_5),
% 1.37/0.54    inference(resolution,[],[f46,f90])).
% 1.37/0.54  fof(f46,plain,(
% 1.37/0.54    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f16])).
% 1.37/0.54  fof(f16,plain,(
% 1.37/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f8])).
% 1.37/0.54  fof(f8,axiom,(
% 1.37/0.54    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.37/0.54  fof(f97,plain,(
% 1.37/0.54    ~spl4_6),
% 1.37/0.54    inference(avatar_split_clause,[],[f43,f94])).
% 1.37/0.54  fof(f43,plain,(
% 1.37/0.54    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))),
% 1.37/0.54    inference(cnf_transformation,[],[f28])).
% 1.37/0.54  fof(f28,plain,(
% 1.37/0.54    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f27])).
% 1.37/0.54  fof(f27,plain,(
% 1.37/0.54    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f13,plain,(
% 1.37/0.54    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.37/0.54    inference(flattening,[],[f12])).
% 1.37/0.54  fof(f12,plain,(
% 1.37/0.54    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f11])).
% 1.37/0.54  fof(f11,negated_conjecture,(
% 1.37/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 1.37/0.54    inference(negated_conjecture,[],[f10])).
% 1.37/0.54  fof(f10,conjecture,(
% 1.37/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).
% 1.37/0.54  fof(f91,plain,(
% 1.37/0.54    spl4_5),
% 1.37/0.54    inference(avatar_split_clause,[],[f42,f88])).
% 1.37/0.54  fof(f42,plain,(
% 1.37/0.54    l1_orders_2(sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f28])).
% 1.37/0.54  fof(f86,plain,(
% 1.37/0.54    spl4_4),
% 1.37/0.54    inference(avatar_split_clause,[],[f41,f83])).
% 1.37/0.54  fof(f41,plain,(
% 1.37/0.54    v5_orders_2(sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f28])).
% 1.37/0.54  fof(f81,plain,(
% 1.37/0.54    spl4_3),
% 1.37/0.54    inference(avatar_split_clause,[],[f40,f78])).
% 1.37/0.54  fof(f40,plain,(
% 1.37/0.54    v4_orders_2(sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f28])).
% 1.37/0.54  fof(f76,plain,(
% 1.37/0.54    spl4_2),
% 1.37/0.54    inference(avatar_split_clause,[],[f39,f73])).
% 1.37/0.54  fof(f39,plain,(
% 1.37/0.54    v3_orders_2(sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f28])).
% 1.37/0.54  fof(f71,plain,(
% 1.37/0.54    ~spl4_1),
% 1.37/0.54    inference(avatar_split_clause,[],[f38,f68])).
% 1.37/0.54  fof(f38,plain,(
% 1.37/0.54    ~v2_struct_0(sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f28])).
% 1.37/0.54  % (24813)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.37/0.54  % SZS output end Proof for theBenchmark
% 1.37/0.54  % (24790)------------------------------
% 1.37/0.54  % (24790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (24790)Termination reason: Refutation
% 1.37/0.54  
% 1.37/0.54  % (24790)Memory used [KB]: 6396
% 1.37/0.54  % (24790)Time elapsed: 0.111 s
% 1.37/0.54  % (24790)------------------------------
% 1.37/0.54  % (24790)------------------------------
% 1.37/0.54  % (24795)Refutation not found, incomplete strategy% (24795)------------------------------
% 1.37/0.54  % (24795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (24787)Success in time 0.179 s
%------------------------------------------------------------------------------
