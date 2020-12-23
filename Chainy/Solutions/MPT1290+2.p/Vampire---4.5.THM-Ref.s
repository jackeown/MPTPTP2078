%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1290+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:16 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   37 (  55 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   78 ( 134 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2341,f2345,f2349,f2358,f2367,f2382,f2387])).

fof(f2387,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tarski(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2382,plain,
    ( spl9_8
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f2377,f2347,f2380])).

fof(f2380,plain,
    ( spl9_8
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f2347,plain,
    ( spl9_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f2377,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl9_3 ),
    inference(resolution,[],[f2326,f2348])).

fof(f2348,plain,
    ( l1_struct_0(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f2347])).

fof(f2326,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2264])).

fof(f2264,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f2367,plain,
    ( spl9_6
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f2361,f2343,f2365])).

fof(f2365,plain,
    ( spl9_6
  <=> r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f2343,plain,
    ( spl9_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f2361,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_2 ),
    inference(resolution,[],[f2302,f2344])).

fof(f2344,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f2343])).

fof(f2302,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2276])).

fof(f2276,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f2358,plain,
    ( ~ spl9_5
    | spl9_1 ),
    inference(avatar_split_clause,[],[f2354,f2339,f2356])).

fof(f2356,plain,
    ( spl9_5
  <=> r1_tarski(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f2339,plain,
    ( spl9_1
  <=> r1_tarski(sK1,k9_setfam_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2354,plain,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1 ),
    inference(backward_demodulation,[],[f2340,f2322])).

fof(f2322,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f2340,plain,
    ( ~ r1_tarski(sK1,k9_setfam_1(k2_struct_0(sK0)))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f2339])).

fof(f2349,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f2297,f2347])).

fof(f2297,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2275])).

fof(f2275,plain,
    ( ~ r1_tarski(sK1,k9_setfam_1(k2_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2249,f2274,f2273])).

fof(f2273,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(X0)))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(sK0)))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2274,plain,
    ( ? [X1] :
        ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(sK0)))
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r1_tarski(sK1,k9_setfam_1(k2_struct_0(sK0)))
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f2249,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(X0)))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2237])).

fof(f2237,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => r1_tarski(X1,k9_setfam_1(k2_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f2236])).

fof(f2236,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => r1_tarski(X1,k9_setfam_1(k2_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tops_2)).

fof(f2345,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f2298,f2343])).

fof(f2298,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f2275])).

fof(f2341,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f2299,f2339])).

fof(f2299,plain,(
    ~ r1_tarski(sK1,k9_setfam_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2275])).
%------------------------------------------------------------------------------
