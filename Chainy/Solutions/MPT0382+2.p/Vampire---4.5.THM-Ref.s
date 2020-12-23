%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0382+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  64 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   82 ( 202 expanded)
%              Number of equality atoms :   34 (  93 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f724,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f676,f680,f684,f688,f714,f718,f723])).

fof(f723,plain,
    ( sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | sK2 != k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f718,plain,
    ( spl13_7
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f704,f686,f716])).

fof(f716,plain,
    ( spl13_7
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f686,plain,
    ( spl13_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f704,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl13_4 ),
    inference(resolution,[],[f642,f687])).

fof(f687,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f686])).

fof(f642,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f560])).

fof(f560,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f486])).

fof(f486,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f714,plain,
    ( spl13_6
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f710,f682,f678,f712])).

fof(f712,plain,
    ( spl13_6
  <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f678,plain,
    ( spl13_2
  <=> k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f682,plain,
    ( spl13_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f710,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(forward_demodulation,[],[f703,f679])).

fof(f679,plain,
    ( k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f678])).

fof(f703,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl13_3 ),
    inference(resolution,[],[f642,f683])).

fof(f683,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f682])).

fof(f688,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f618,f686])).

fof(f618,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f584])).

fof(f584,plain,
    ( sK1 != sK2
    & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f540,f583,f582])).

fof(f582,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f583,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != sK2
      & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f540,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f539])).

fof(f539,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f536])).

fof(f536,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f535])).

fof(f535,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_subset_1)).

fof(f684,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f619,f682])).

fof(f619,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f584])).

fof(f680,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f620,f678])).

fof(f620,plain,(
    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f584])).

fof(f676,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f621,f674])).

fof(f674,plain,
    ( spl13_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f621,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f584])).
%------------------------------------------------------------------------------
