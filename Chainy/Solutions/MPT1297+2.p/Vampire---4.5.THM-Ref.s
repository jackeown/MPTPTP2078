%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1297+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:17 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 124 expanded)
%              Number of leaves         :    6 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 627 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2594,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2593,f2386])).

fof(f2386,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f2331])).

fof(f2331,plain,
    ( ( ~ v1_finset_1(sK3)
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK2),sK3)) )
    & ( v1_finset_1(sK3)
      | v1_finset_1(k7_setfam_1(u1_struct_0(sK2),sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f2328,f2330,f2329])).

fof(f2329,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_finset_1(X1)
              | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
            & ( v1_finset_1(X1)
              | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK2),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(sK2),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2330,plain,
    ( ? [X1] :
        ( ( ~ v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK2),X1)) )
        & ( v1_finset_1(X1)
          | v1_finset_1(k7_setfam_1(u1_struct_0(sK2),X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ( ~ v1_finset_1(sK3)
        | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK2),sK3)) )
      & ( v1_finset_1(sK3)
        | v1_finset_1(k7_setfam_1(u1_struct_0(sK2),sK3)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f2328,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f2327])).

fof(f2327,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2257])).

fof(f2257,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <~> v1_finset_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2248])).

fof(f2248,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
            <=> v1_finset_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f2247])).

fof(f2247,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tops_2)).

fof(f2593,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f2582,f2475])).

fof(f2475,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2309])).

fof(f2309,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f565])).

fof(f565,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f2582,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f2581,f2385])).

fof(f2385,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f2331])).

fof(f2581,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f2580,f2563])).

fof(f2563,plain,(
    ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK2),sK3)) ),
    inference(subsumption_resolution,[],[f2388,f2562])).

fof(f2562,plain,(
    v1_finset_1(sK3) ),
    inference(subsumption_resolution,[],[f2561,f2385])).

fof(f2561,plain,
    ( v1_finset_1(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f2560,f2386])).

fof(f2560,plain,
    ( v1_finset_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f2558])).

fof(f2558,plain,
    ( v1_finset_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_struct_0(sK2)
    | v1_finset_1(sK3) ),
    inference(resolution,[],[f2477,f2387])).

fof(f2387,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(sK2),sK3))
    | v1_finset_1(sK3) ),
    inference(cnf_transformation,[],[f2331])).

fof(f2477,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
      | v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2312])).

fof(f2312,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f2311])).

fof(f2311,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2237])).

fof(f2237,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
           => v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_tops_2)).

fof(f2388,plain,
    ( ~ v1_finset_1(sK3)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK2),sK3)) ),
    inference(cnf_transformation,[],[f2331])).

fof(f2580,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(sK2),sK3))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f2577,f2562])).

fof(f2577,plain,
    ( ~ v1_finset_1(sK3)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK2),sK3))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_struct_0(sK2) ),
    inference(superposition,[],[f2477,f2536])).

fof(f2536,plain,(
    sK3 = k7_setfam_1(u1_struct_0(sK2),k7_setfam_1(u1_struct_0(sK2),sK3)) ),
    inference(resolution,[],[f2476,f2386])).

fof(f2476,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2310])).

fof(f2310,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f574])).

fof(f574,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
%------------------------------------------------------------------------------
