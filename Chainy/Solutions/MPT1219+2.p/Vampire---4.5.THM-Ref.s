%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1219+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   35 (  68 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   97 ( 262 expanded)
%              Number of equality atoms :   38 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2190,f2194,f2198,f2202,f2229,f2233,f2238])).

fof(f2238,plain,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | sK2 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2233,plain,
    ( spl9_9
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f2220,f2200,f2231])).

fof(f2231,plain,
    ( spl9_9
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f2200,plain,
    ( spl9_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f2220,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl9_4 ),
    inference(resolution,[],[f2176,f2201])).

fof(f2201,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f2200])).

fof(f2176,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2113])).

fof(f2113,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2229,plain,
    ( spl9_8
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f2225,f2196,f2192,f2227])).

fof(f2227,plain,
    ( spl9_8
  <=> sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f2192,plain,
    ( spl9_2
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f2196,plain,
    ( spl9_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f2225,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f2219,f2193])).

fof(f2193,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f2192])).

fof(f2219,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl9_3 ),
    inference(resolution,[],[f2176,f2197])).

fof(f2197,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f2196])).

fof(f2202,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f2151,f2200])).

fof(f2151,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2128])).

fof(f2128,plain,
    ( sK1 != sK2
    & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2091,f2127,f2126,f2125])).

fof(f2125,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k3_subset_1(u1_struct_0(sK0),X1) = k3_subset_1(u1_struct_0(sK0),X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2126,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & k3_subset_1(u1_struct_0(sK0),X1) = k3_subset_1(u1_struct_0(sK0),X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & k3_subset_1(u1_struct_0(sK0),X2) = k3_subset_1(u1_struct_0(sK0),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2127,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k3_subset_1(u1_struct_0(sK0),X2) = k3_subset_1(u1_struct_0(sK0),sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( sK1 != sK2
      & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2091,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f2090])).

fof(f2090,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2087])).

fof(f2087,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f2086])).

fof(f2086,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tops_1)).

fof(f2198,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f2152,f2196])).

fof(f2152,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2128])).

fof(f2194,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f2153,f2192])).

fof(f2153,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(cnf_transformation,[],[f2128])).

fof(f2190,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f2154,f2188])).

fof(f2188,plain,
    ( spl9_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2154,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f2128])).
%------------------------------------------------------------------------------
