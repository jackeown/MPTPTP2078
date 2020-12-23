%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t8_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:27 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 245 expanded)
%              Number of leaves         :   13 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  263 (1524 expanded)
%              Number of equality atoms :   19 ( 176 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f107,f127,f156,f176,f204,f208])).

fof(f208,plain,
    ( ~ spl5_4
    | spl5_7
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f146,f79])).

fof(f79,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_7
  <=> ~ r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f146,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f145,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).

fof(f23,plain,
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

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( sK2 != X1
        & ! [X3] :
            ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,sK2) )
              & ( r2_hidden(X3,sK2)
                | ~ r2_hidden(X3,X1) ) )
            | ~ m1_subset_1(X3,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t8_subset_1.p',t8_subset_1)).

fof(f145,plain,
    ( r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f141,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f141,plain,
    ( r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(resolution,[],[f111,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK4(X0,X1,X2),X2)
            & r2_hidden(sK4(X0,X1,X2),X1)
            & m1_subset_1(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t8_subset_1.p',t7_subset_1)).

fof(f111,plain,
    ( r2_hidden(sK4(sK0,sK2,sK1),sK1)
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f108,f76])).

fof(f76,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK1),sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_4
  <=> m1_subset_1(sK4(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f108,plain,
    ( r2_hidden(sK4(sK0,sK2,sK1),sK1)
    | ~ m1_subset_1(sK4(sK0,sK2,sK1),sK0)
    | ~ spl5_12 ),
    inference(resolution,[],[f106,f35])).

fof(f35,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f106,plain,
    ( r2_hidden(sK4(sK0,sK2,sK1),sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_12
  <=> r2_hidden(sK4(sK0,sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f204,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f202,f32])).

fof(f202,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f201,f33])).

fof(f201,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f197,f178])).

fof(f178,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f177,f36])).

fof(f36,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f177,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f82,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/subset_1__t8_subset_1.p',d10_xboole_0)).

fof(f82,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_6
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f197,plain,
    ( r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(resolution,[],[f196,f43])).

fof(f196,plain,
    ( r2_hidden(sK4(sK0,sK1,sK2),sK2)
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f193,f120])).

fof(f120,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_14
  <=> m1_subset_1(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f193,plain,
    ( r2_hidden(sK4(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),sK0)
    | ~ spl5_22 ),
    inference(resolution,[],[f155,f34])).

fof(f34,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f155,plain,
    ( r2_hidden(sK4(sK0,sK1,sK2),sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_22
  <=> r2_hidden(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f176,plain,
    ( ~ spl5_6
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f82,f165])).

fof(f165,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f164,f36])).

fof(f164,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK2,sK1)
    | ~ spl5_16 ),
    inference(resolution,[],[f126,f46])).

fof(f126,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_16
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f156,plain,
    ( spl5_22
    | spl5_16 ),
    inference(avatar_split_clause,[],[f147,f125,f154])).

fof(f147,plain,
    ( r1_tarski(sK1,sK2)
    | r2_hidden(sK4(sK0,sK1,sK2),sK1) ),
    inference(resolution,[],[f54,f32])).

fof(f54,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r1_tarski(X1,sK2)
      | r2_hidden(sK4(sK0,X1,sK2),X1) ) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f127,plain,
    ( spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f112,f125,f119])).

fof(f112,plain,
    ( r1_tarski(sK1,sK2)
    | m1_subset_1(sK4(sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f53,f32])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(X0,sK2)
      | m1_subset_1(sK4(sK0,X0,sK2),sK0) ) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f107,plain,
    ( spl5_12
    | spl5_6 ),
    inference(avatar_split_clause,[],[f99,f81,f105])).

fof(f99,plain,
    ( r1_tarski(sK2,sK1)
    | r2_hidden(sK4(sK0,sK2,sK1),sK2) ),
    inference(resolution,[],[f52,f33])).

fof(f52,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r1_tarski(X1,sK1)
      | r2_hidden(sK4(sK0,X1,sK1),X1) ) ),
    inference(resolution,[],[f32,f42])).

fof(f83,plain,
    ( spl5_4
    | spl5_6 ),
    inference(avatar_split_clause,[],[f57,f81,f75])).

fof(f57,plain,
    ( r1_tarski(sK2,sK1)
    | m1_subset_1(sK4(sK0,sK2,sK1),sK0) ),
    inference(resolution,[],[f51,f33])).

fof(f51,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(X0,sK1)
      | m1_subset_1(sK4(sK0,X0,sK1),sK0) ) ),
    inference(resolution,[],[f32,f41])).
%------------------------------------------------------------------------------
