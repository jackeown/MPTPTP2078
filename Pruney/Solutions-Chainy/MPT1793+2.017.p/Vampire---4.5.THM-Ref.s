%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:29 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 613 expanded)
%              Number of leaves         :   28 ( 264 expanded)
%              Depth                    :   14
%              Number of atoms          :  698 (4766 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f337,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f129,f240,f250,f260,f269,f284,f293,f298,f309,f327,f336])).

fof(f336,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f334,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & r1_xboole_0(u1_struct_0(sK2),sK1)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
                & r1_xboole_0(u1_struct_0(X2),X1)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_xboole_0(u1_struct_0(X2),X1)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_xboole_0(u1_struct_0(X2),sK1)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

% (8798)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3)
            & m1_subset_1(X3,u1_struct_0(X2)) )
        & r1_xboole_0(u1_struct_0(X2),sK1)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3)
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & r1_xboole_0(u1_struct_0(sK2),sK1)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3)
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_xboole_0(u1_struct_0(X2),X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).

fof(f334,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f333,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f333,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f332,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f332,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f329,f48])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f329,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f215,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f215,plain,
    ( v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl6_3
  <=> v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f327,plain,
    ( ~ spl6_2
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f317,f130])).

fof(f130,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl6_2 ),
    inference(resolution,[],[f124,f52])).

fof(f52,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f124,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r2_hidden(X1,u1_struct_0(sK2)) )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_2
  <=> ! [X1] :
        ( r2_hidden(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f317,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl6_11 ),
    inference(resolution,[],[f283,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f62,f51])).

fof(f51,plain,(
    r1_xboole_0(u1_struct_0(sK2),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f283,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl6_11
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f309,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl6_8 ),
    inference(subsumption_resolution,[],[f307,f45])).

fof(f307,plain,
    ( v2_struct_0(sK0)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f306,f46])).

fof(f306,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f305,f47])).

fof(f305,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f302,f48])).

fof(f302,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_8 ),
    inference(resolution,[],[f235,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f235,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl6_8
  <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f298,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f45,f47,f49,f50,f52,f279,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f279,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f293,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | spl6_7 ),
    inference(subsumption_resolution,[],[f291,f45])).

fof(f291,plain,
    ( v2_struct_0(sK0)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f290,f46])).

fof(f290,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f289,f47])).

fof(f289,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7 ),
    inference(subsumption_resolution,[],[f286,f48])).

fof(f286,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_7 ),
    inference(resolution,[],[f231,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f231,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl6_7
  <=> v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f284,plain,
    ( ~ spl6_10
    | spl6_11
    | spl6_9 ),
    inference(avatar_split_clause,[],[f275,f237,f281,f277])).

fof(f237,plain,
    ( spl6_9
  <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f275,plain,
    ( r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | spl6_9 ),
    inference(subsumption_resolution,[],[f274,f45])).

fof(f274,plain,
    ( r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl6_9 ),
    inference(subsumption_resolution,[],[f273,f46])).

fof(f273,plain,
    ( r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_9 ),
    inference(subsumption_resolution,[],[f272,f47])).

fof(f272,plain,
    ( r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_9 ),
    inference(subsumption_resolution,[],[f270,f48])).

fof(f270,plain,
    ( r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_9 ),
    inference(resolution,[],[f239,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ r2_hidden(X2,X1)
               => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_tmap_1)).

fof(f239,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f237])).

fof(f269,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | spl6_6 ),
    inference(subsumption_resolution,[],[f267,f45])).

fof(f267,plain,
    ( v2_struct_0(sK0)
    | spl6_6 ),
    inference(subsumption_resolution,[],[f266,f46])).

fof(f266,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_6 ),
    inference(subsumption_resolution,[],[f265,f47])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_6 ),
    inference(subsumption_resolution,[],[f262,f48])).

fof(f262,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_6 ),
    inference(resolution,[],[f227,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f227,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl6_6
  <=> v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f260,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | spl6_5 ),
    inference(subsumption_resolution,[],[f258,f45])).

fof(f258,plain,
    ( v2_struct_0(sK0)
    | spl6_5 ),
    inference(subsumption_resolution,[],[f257,f46])).

fof(f257,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_5 ),
    inference(subsumption_resolution,[],[f256,f47])).

fof(f256,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_5 ),
    inference(subsumption_resolution,[],[f252,f48])).

fof(f252,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_5 ),
    inference(resolution,[],[f223,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f223,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl6_5
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f250,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f248,f45])).

fof(f248,plain,
    ( v2_struct_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f247,f46])).

fof(f247,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f246,f47])).

fof(f246,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f243,f48])).

fof(f243,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_4 ),
    inference(resolution,[],[f219,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f219,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl6_4
  <=> v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f240,plain,
    ( spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f188,f237,f233,f229,f225,f221,f217,f213])).

fof(f188,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f187,f45])).

fof(f187,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f186,f46])).

fof(f186,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f185,f47])).

fof(f185,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f184,f49])).

fof(f184,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f183,f50])).

fof(f183,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f182,f52])).

fof(f182,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f178,f53])).

fof(f53,plain,(
    ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f178,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f71,f59])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f129,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f47,f50,f121,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f121,plain,
    ( ~ l1_pre_topc(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_1
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f125,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f114,f123,f119])).

fof(f114,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f112,f49])).

fof(f112,plain,(
    ! [X4,X3] :
      ( v2_struct_0(X4)
      | r2_hidden(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f104,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_hidden(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f63,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:22:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.41  % (8784)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.42  % (8790)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.18/0.42  % (8784)Refutation found. Thanks to Tanya!
% 0.18/0.42  % SZS status Theorem for theBenchmark
% 0.18/0.43  % (8792)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.43  % SZS output start Proof for theBenchmark
% 0.18/0.43  fof(f337,plain,(
% 0.18/0.43    $false),
% 0.18/0.43    inference(avatar_sat_refutation,[],[f125,f129,f240,f250,f260,f269,f284,f293,f298,f309,f327,f336])).
% 0.18/0.43  fof(f336,plain,(
% 0.18/0.43    ~spl6_3),
% 0.18/0.43    inference(avatar_contradiction_clause,[],[f335])).
% 0.18/0.43  fof(f335,plain,(
% 0.18/0.43    $false | ~spl6_3),
% 0.18/0.43    inference(subsumption_resolution,[],[f334,f45])).
% 0.18/0.43  fof(f45,plain,(
% 0.18/0.43    ~v2_struct_0(sK0)),
% 0.18/0.43    inference(cnf_transformation,[],[f42])).
% 0.18/0.43  fof(f42,plain,(
% 0.18/0.43    (((~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2))) & r1_xboole_0(u1_struct_0(sK2),sK1) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.18/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f41,f40,f39,f38])).
% 0.18/0.43  fof(f38,plain,(
% 0.18/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.18/0.43    introduced(choice_axiom,[])).
% 0.18/0.43  fof(f39,plain,(
% 0.18/0.43    ? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.18/0.43    introduced(choice_axiom,[])).
% 0.18/0.43  % (8798)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.18/0.43  fof(f40,plain,(
% 0.18/0.43    ? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),sK1) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) & r1_xboole_0(u1_struct_0(sK2),sK1) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.18/0.43    introduced(choice_axiom,[])).
% 0.18/0.43  fof(f41,plain,(
% 0.18/0.43    ? [X3] : (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.18/0.43    introduced(choice_axiom,[])).
% 0.18/0.43  fof(f18,plain,(
% 0.18/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.18/0.43    inference(flattening,[],[f17])).
% 0.18/0.43  fof(f17,plain,(
% 0.18/0.43    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.18/0.43    inference(ennf_transformation,[],[f13])).
% 0.18/0.43  fof(f13,negated_conjecture,(
% 0.18/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 0.18/0.43    inference(negated_conjecture,[],[f12])).
% 0.18/0.43  fof(f12,conjecture,(
% 0.18/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).
% 0.18/0.43  fof(f334,plain,(
% 0.18/0.43    v2_struct_0(sK0) | ~spl6_3),
% 0.18/0.43    inference(subsumption_resolution,[],[f333,f46])).
% 0.18/0.43  fof(f46,plain,(
% 0.18/0.43    v2_pre_topc(sK0)),
% 0.18/0.43    inference(cnf_transformation,[],[f42])).
% 0.18/0.43  fof(f333,plain,(
% 0.18/0.43    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_3),
% 0.18/0.43    inference(subsumption_resolution,[],[f332,f47])).
% 0.18/0.43  fof(f47,plain,(
% 0.18/0.43    l1_pre_topc(sK0)),
% 0.18/0.43    inference(cnf_transformation,[],[f42])).
% 0.18/0.43  fof(f332,plain,(
% 0.18/0.43    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_3),
% 0.18/0.43    inference(subsumption_resolution,[],[f329,f48])).
% 0.18/0.43  fof(f48,plain,(
% 0.18/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.43    inference(cnf_transformation,[],[f42])).
% 0.18/0.43  fof(f329,plain,(
% 0.18/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_3),
% 0.18/0.43    inference(resolution,[],[f215,f64])).
% 0.18/0.43  fof(f64,plain,(
% 0.18/0.43    ( ! [X0,X1] : (~v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f33])).
% 0.18/0.43  fof(f33,plain,(
% 0.18/0.43    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.18/0.43    inference(flattening,[],[f32])).
% 0.18/0.43  fof(f32,plain,(
% 0.18/0.43    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.18/0.43    inference(ennf_transformation,[],[f16])).
% 0.18/0.43  fof(f16,plain,(
% 0.18/0.43    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 0.18/0.43    inference(pure_predicate_removal,[],[f9])).
% 0.18/0.43  fof(f9,axiom,(
% 0.18/0.43    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).
% 0.18/0.43  fof(f215,plain,(
% 0.18/0.43    v2_struct_0(k6_tmap_1(sK0,sK1)) | ~spl6_3),
% 0.18/0.43    inference(avatar_component_clause,[],[f213])).
% 0.18/0.43  fof(f213,plain,(
% 0.18/0.43    spl6_3 <=> v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.18/0.43  fof(f327,plain,(
% 0.18/0.43    ~spl6_2 | ~spl6_11),
% 0.18/0.43    inference(avatar_contradiction_clause,[],[f326])).
% 0.18/0.43  fof(f326,plain,(
% 0.18/0.43    $false | (~spl6_2 | ~spl6_11)),
% 0.18/0.43    inference(subsumption_resolution,[],[f317,f130])).
% 0.18/0.43  fof(f130,plain,(
% 0.18/0.43    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl6_2),
% 0.18/0.43    inference(resolution,[],[f124,f52])).
% 0.18/0.43  fof(f52,plain,(
% 0.18/0.43    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.18/0.43    inference(cnf_transformation,[],[f42])).
% 0.18/0.43  fof(f124,plain,(
% 0.18/0.43    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK2)) | r2_hidden(X1,u1_struct_0(sK2))) ) | ~spl6_2),
% 0.18/0.43    inference(avatar_component_clause,[],[f123])).
% 0.18/0.43  fof(f123,plain,(
% 0.18/0.43    spl6_2 <=> ! [X1] : (r2_hidden(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)))),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.18/0.43  fof(f317,plain,(
% 0.18/0.43    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~spl6_11),
% 0.18/0.43    inference(resolution,[],[f283,f96])).
% 0.18/0.43  fof(f96,plain,(
% 0.18/0.43    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,u1_struct_0(sK2))) )),
% 0.18/0.43    inference(resolution,[],[f62,f51])).
% 0.18/0.43  fof(f51,plain,(
% 0.18/0.43    r1_xboole_0(u1_struct_0(sK2),sK1)),
% 0.18/0.43    inference(cnf_transformation,[],[f42])).
% 0.18/0.43  fof(f62,plain,(
% 0.18/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f44])).
% 0.18/0.43  fof(f44,plain,(
% 0.18/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.18/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f43])).
% 0.18/0.43  fof(f43,plain,(
% 0.18/0.43    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.18/0.43    introduced(choice_axiom,[])).
% 0.18/0.43  fof(f29,plain,(
% 0.18/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.18/0.43    inference(ennf_transformation,[],[f14])).
% 0.18/0.43  fof(f14,plain,(
% 0.18/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.43    inference(rectify,[],[f1])).
% 0.18/0.43  fof(f1,axiom,(
% 0.18/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.18/0.43  fof(f283,plain,(
% 0.18/0.43    r2_hidden(sK3,sK1) | ~spl6_11),
% 0.18/0.43    inference(avatar_component_clause,[],[f281])).
% 0.18/0.43  fof(f281,plain,(
% 0.18/0.43    spl6_11 <=> r2_hidden(sK3,sK1)),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.18/0.43  fof(f309,plain,(
% 0.18/0.43    spl6_8),
% 0.18/0.43    inference(avatar_contradiction_clause,[],[f308])).
% 0.18/0.43  fof(f308,plain,(
% 0.18/0.43    $false | spl6_8),
% 0.18/0.43    inference(subsumption_resolution,[],[f307,f45])).
% 0.18/0.43  fof(f307,plain,(
% 0.18/0.43    v2_struct_0(sK0) | spl6_8),
% 0.18/0.43    inference(subsumption_resolution,[],[f306,f46])).
% 0.18/0.43  fof(f306,plain,(
% 0.18/0.43    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_8),
% 0.18/0.43    inference(subsumption_resolution,[],[f305,f47])).
% 0.18/0.43  fof(f305,plain,(
% 0.18/0.43    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_8),
% 0.18/0.43    inference(subsumption_resolution,[],[f302,f48])).
% 0.18/0.43  fof(f302,plain,(
% 0.18/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_8),
% 0.18/0.43    inference(resolution,[],[f235,f68])).
% 0.18/0.43  fof(f68,plain,(
% 0.18/0.43    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f35])).
% 0.18/0.43  fof(f35,plain,(
% 0.18/0.43    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.18/0.43    inference(flattening,[],[f34])).
% 0.18/0.43  fof(f34,plain,(
% 0.18/0.43    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.18/0.43    inference(ennf_transformation,[],[f8])).
% 0.18/0.43  fof(f8,axiom,(
% 0.18/0.43    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 0.18/0.43  fof(f235,plain,(
% 0.18/0.43    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | spl6_8),
% 0.18/0.43    inference(avatar_component_clause,[],[f233])).
% 0.18/0.43  fof(f233,plain,(
% 0.18/0.43    spl6_8 <=> m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.18/0.43  fof(f298,plain,(
% 0.18/0.43    spl6_10),
% 0.18/0.43    inference(avatar_contradiction_clause,[],[f295])).
% 0.18/0.43  fof(f295,plain,(
% 0.18/0.43    $false | spl6_10),
% 0.18/0.43    inference(unit_resulting_resolution,[],[f45,f47,f49,f50,f52,f279,f59])).
% 0.18/0.43  fof(f59,plain,(
% 0.18/0.43    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f28])).
% 0.18/0.43  fof(f28,plain,(
% 0.18/0.43    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.18/0.43    inference(flattening,[],[f27])).
% 0.18/0.43  fof(f27,plain,(
% 0.18/0.43    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.18/0.43    inference(ennf_transformation,[],[f6])).
% 0.18/0.43  fof(f6,axiom,(
% 0.18/0.43    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.18/0.43  fof(f279,plain,(
% 0.18/0.43    ~m1_subset_1(sK3,u1_struct_0(sK0)) | spl6_10),
% 0.18/0.43    inference(avatar_component_clause,[],[f277])).
% 0.18/0.43  fof(f277,plain,(
% 0.18/0.43    spl6_10 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.18/0.43  fof(f50,plain,(
% 0.18/0.43    m1_pre_topc(sK2,sK0)),
% 0.18/0.43    inference(cnf_transformation,[],[f42])).
% 0.18/0.43  fof(f49,plain,(
% 0.18/0.43    ~v2_struct_0(sK2)),
% 0.18/0.43    inference(cnf_transformation,[],[f42])).
% 0.18/0.43  fof(f293,plain,(
% 0.18/0.43    spl6_7),
% 0.18/0.43    inference(avatar_contradiction_clause,[],[f292])).
% 0.18/0.43  fof(f292,plain,(
% 0.18/0.43    $false | spl6_7),
% 0.18/0.43    inference(subsumption_resolution,[],[f291,f45])).
% 0.18/0.43  fof(f291,plain,(
% 0.18/0.43    v2_struct_0(sK0) | spl6_7),
% 0.18/0.43    inference(subsumption_resolution,[],[f290,f46])).
% 0.18/0.43  fof(f290,plain,(
% 0.18/0.43    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_7),
% 0.18/0.43    inference(subsumption_resolution,[],[f289,f47])).
% 0.18/0.43  fof(f289,plain,(
% 0.18/0.43    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_7),
% 0.18/0.43    inference(subsumption_resolution,[],[f286,f48])).
% 0.18/0.43  fof(f286,plain,(
% 0.18/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_7),
% 0.18/0.43    inference(resolution,[],[f231,f67])).
% 0.18/0.43  fof(f67,plain,(
% 0.18/0.43    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f35])).
% 0.18/0.43  fof(f231,plain,(
% 0.18/0.43    ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | spl6_7),
% 0.18/0.43    inference(avatar_component_clause,[],[f229])).
% 0.18/0.43  fof(f229,plain,(
% 0.18/0.43    spl6_7 <=> v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.18/0.43  fof(f284,plain,(
% 0.18/0.43    ~spl6_10 | spl6_11 | spl6_9),
% 0.18/0.43    inference(avatar_split_clause,[],[f275,f237,f281,f277])).
% 0.18/0.43  fof(f237,plain,(
% 0.18/0.43    spl6_9 <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.18/0.43  fof(f275,plain,(
% 0.18/0.43    r2_hidden(sK3,sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | spl6_9),
% 0.18/0.43    inference(subsumption_resolution,[],[f274,f45])).
% 0.18/0.43  fof(f274,plain,(
% 0.18/0.43    r2_hidden(sK3,sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | spl6_9),
% 0.18/0.43    inference(subsumption_resolution,[],[f273,f46])).
% 0.18/0.43  fof(f273,plain,(
% 0.18/0.43    r2_hidden(sK3,sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_9),
% 0.18/0.43    inference(subsumption_resolution,[],[f272,f47])).
% 0.18/0.43  fof(f272,plain,(
% 0.18/0.43    r2_hidden(sK3,sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_9),
% 0.18/0.43    inference(subsumption_resolution,[],[f270,f48])).
% 0.18/0.43  fof(f270,plain,(
% 0.18/0.43    r2_hidden(sK3,sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_9),
% 0.18/0.43    inference(resolution,[],[f239,f57])).
% 0.18/0.43  fof(f57,plain,(
% 0.18/0.43    ( ! [X2,X0,X1] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f24])).
% 0.18/0.43  fof(f24,plain,(
% 0.18/0.43    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.18/0.43    inference(flattening,[],[f23])).
% 0.18/0.43  fof(f23,plain,(
% 0.18/0.43    ! [X0] : (! [X1] : (! [X2] : ((r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.18/0.43    inference(ennf_transformation,[],[f10])).
% 0.18/0.43  fof(f10,axiom,(
% 0.18/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~r2_hidden(X2,X1) => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_tmap_1)).
% 0.18/0.43  fof(f239,plain,(
% 0.18/0.43    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | spl6_9),
% 0.18/0.43    inference(avatar_component_clause,[],[f237])).
% 0.18/0.43  fof(f269,plain,(
% 0.18/0.43    spl6_6),
% 0.18/0.43    inference(avatar_contradiction_clause,[],[f268])).
% 0.18/0.43  fof(f268,plain,(
% 0.18/0.43    $false | spl6_6),
% 0.18/0.43    inference(subsumption_resolution,[],[f267,f45])).
% 0.18/0.43  fof(f267,plain,(
% 0.18/0.43    v2_struct_0(sK0) | spl6_6),
% 0.18/0.43    inference(subsumption_resolution,[],[f266,f46])).
% 0.18/0.43  fof(f266,plain,(
% 0.18/0.43    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_6),
% 0.18/0.43    inference(subsumption_resolution,[],[f265,f47])).
% 0.18/0.43  fof(f265,plain,(
% 0.18/0.43    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_6),
% 0.18/0.43    inference(subsumption_resolution,[],[f262,f48])).
% 0.18/0.43  fof(f262,plain,(
% 0.18/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_6),
% 0.18/0.43    inference(resolution,[],[f227,f66])).
% 0.18/0.43  fof(f66,plain,(
% 0.18/0.43    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f35])).
% 0.18/0.43  fof(f227,plain,(
% 0.18/0.43    ~v1_funct_1(k7_tmap_1(sK0,sK1)) | spl6_6),
% 0.18/0.43    inference(avatar_component_clause,[],[f225])).
% 0.18/0.43  fof(f225,plain,(
% 0.18/0.43    spl6_6 <=> v1_funct_1(k7_tmap_1(sK0,sK1))),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.18/0.43  fof(f260,plain,(
% 0.18/0.43    spl6_5),
% 0.18/0.43    inference(avatar_contradiction_clause,[],[f259])).
% 0.18/0.43  fof(f259,plain,(
% 0.18/0.43    $false | spl6_5),
% 0.18/0.43    inference(subsumption_resolution,[],[f258,f45])).
% 0.18/0.43  fof(f258,plain,(
% 0.18/0.43    v2_struct_0(sK0) | spl6_5),
% 0.18/0.43    inference(subsumption_resolution,[],[f257,f46])).
% 0.18/0.43  fof(f257,plain,(
% 0.18/0.43    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_5),
% 0.18/0.43    inference(subsumption_resolution,[],[f256,f47])).
% 0.18/0.43  fof(f256,plain,(
% 0.18/0.43    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_5),
% 0.18/0.43    inference(subsumption_resolution,[],[f252,f48])).
% 0.18/0.43  fof(f252,plain,(
% 0.18/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_5),
% 0.18/0.43    inference(resolution,[],[f223,f70])).
% 0.18/0.43  fof(f70,plain,(
% 0.18/0.43    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f37])).
% 0.18/0.43  fof(f37,plain,(
% 0.18/0.43    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.18/0.43    inference(flattening,[],[f36])).
% 0.18/0.43  fof(f36,plain,(
% 0.18/0.43    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.18/0.43    inference(ennf_transformation,[],[f15])).
% 0.18/0.43  fof(f15,plain,(
% 0.18/0.43    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 0.18/0.43    inference(pure_predicate_removal,[],[f7])).
% 0.18/0.43  fof(f7,axiom,(
% 0.18/0.43    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.18/0.43  fof(f223,plain,(
% 0.18/0.43    ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | spl6_5),
% 0.18/0.43    inference(avatar_component_clause,[],[f221])).
% 0.18/0.43  fof(f221,plain,(
% 0.18/0.43    spl6_5 <=> l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.18/0.43  fof(f250,plain,(
% 0.18/0.43    spl6_4),
% 0.18/0.43    inference(avatar_contradiction_clause,[],[f249])).
% 0.18/0.43  fof(f249,plain,(
% 0.18/0.43    $false | spl6_4),
% 0.18/0.43    inference(subsumption_resolution,[],[f248,f45])).
% 0.18/0.43  fof(f248,plain,(
% 0.18/0.43    v2_struct_0(sK0) | spl6_4),
% 0.18/0.43    inference(subsumption_resolution,[],[f247,f46])).
% 0.18/0.43  fof(f247,plain,(
% 0.18/0.43    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_4),
% 0.18/0.43    inference(subsumption_resolution,[],[f246,f47])).
% 0.18/0.43  fof(f246,plain,(
% 0.18/0.43    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_4),
% 0.18/0.43    inference(subsumption_resolution,[],[f243,f48])).
% 0.18/0.43  fof(f243,plain,(
% 0.18/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_4),
% 0.18/0.43    inference(resolution,[],[f219,f65])).
% 0.18/0.43  fof(f65,plain,(
% 0.18/0.43    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f33])).
% 0.18/0.43  fof(f219,plain,(
% 0.18/0.43    ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | spl6_4),
% 0.18/0.43    inference(avatar_component_clause,[],[f217])).
% 0.18/0.43  fof(f217,plain,(
% 0.18/0.43    spl6_4 <=> v2_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.18/0.43  fof(f240,plain,(
% 0.18/0.43    spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.18/0.43    inference(avatar_split_clause,[],[f188,f237,f233,f229,f225,f221,f217,f213])).
% 0.18/0.43  fof(f188,plain,(
% 0.18/0.43    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.18/0.43    inference(subsumption_resolution,[],[f187,f45])).
% 0.18/0.43  fof(f187,plain,(
% 0.18/0.43    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.18/0.43    inference(subsumption_resolution,[],[f186,f46])).
% 0.18/0.43  fof(f186,plain,(
% 0.18/0.43    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.18/0.43    inference(subsumption_resolution,[],[f185,f47])).
% 0.18/0.43  fof(f185,plain,(
% 0.18/0.43    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.18/0.43    inference(subsumption_resolution,[],[f184,f49])).
% 0.18/0.43  fof(f184,plain,(
% 0.18/0.43    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | v2_struct_0(sK2) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.18/0.43    inference(subsumption_resolution,[],[f183,f50])).
% 0.18/0.43  fof(f183,plain,(
% 0.18/0.43    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.18/0.43    inference(subsumption_resolution,[],[f182,f52])).
% 0.18/0.43  fof(f182,plain,(
% 0.18/0.43    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(k6_tmap_1(sK0,sK1))),
% 0.18/0.43    inference(resolution,[],[f178,f53])).
% 0.18/0.43  fof(f53,plain,(
% 0.18/0.43    ~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)),
% 0.18/0.43    inference(cnf_transformation,[],[f42])).
% 0.18/0.43  fof(f178,plain,(
% 0.18/0.43    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(subsumption_resolution,[],[f71,f59])).
% 0.18/0.43  fof(f71,plain,(
% 0.18/0.43    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(equality_resolution,[],[f58])).
% 0.18/0.43  fof(f58,plain,(
% 0.18/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f26])).
% 0.18/0.43  fof(f26,plain,(
% 0.18/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.18/0.43    inference(flattening,[],[f25])).
% 0.18/0.43  fof(f25,plain,(
% 0.18/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.18/0.43    inference(ennf_transformation,[],[f11])).
% 0.18/0.43  fof(f11,axiom,(
% 0.18/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.18/0.43  fof(f129,plain,(
% 0.18/0.43    spl6_1),
% 0.18/0.43    inference(avatar_contradiction_clause,[],[f126])).
% 0.18/0.43  fof(f126,plain,(
% 0.18/0.43    $false | spl6_1),
% 0.18/0.43    inference(unit_resulting_resolution,[],[f47,f50,f121,f55])).
% 0.18/0.43  fof(f55,plain,(
% 0.18/0.43    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f20])).
% 0.18/0.43  fof(f20,plain,(
% 0.18/0.43    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.18/0.43    inference(ennf_transformation,[],[f4])).
% 0.18/0.43  fof(f4,axiom,(
% 0.18/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.18/0.43  fof(f121,plain,(
% 0.18/0.43    ~l1_pre_topc(sK2) | spl6_1),
% 0.18/0.43    inference(avatar_component_clause,[],[f119])).
% 0.18/0.43  fof(f119,plain,(
% 0.18/0.43    spl6_1 <=> l1_pre_topc(sK2)),
% 0.18/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.18/0.43  fof(f125,plain,(
% 0.18/0.43    ~spl6_1 | spl6_2),
% 0.18/0.43    inference(avatar_split_clause,[],[f114,f123,f119])).
% 0.18/0.43  fof(f114,plain,(
% 0.18/0.43    ( ! [X1] : (r2_hidden(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~l1_pre_topc(sK2)) )),
% 0.18/0.43    inference(resolution,[],[f112,f49])).
% 0.18/0.43  fof(f112,plain,(
% 0.18/0.43    ( ! [X4,X3] : (v2_struct_0(X4) | r2_hidden(X3,u1_struct_0(X4)) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~l1_pre_topc(X4)) )),
% 0.18/0.43    inference(resolution,[],[f104,f54])).
% 0.18/0.43  fof(f54,plain,(
% 0.18/0.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f19])).
% 0.18/0.43  fof(f19,plain,(
% 0.18/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.18/0.43    inference(ennf_transformation,[],[f3])).
% 0.18/0.43  fof(f3,axiom,(
% 0.18/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.18/0.43  fof(f104,plain,(
% 0.18/0.43    ( ! [X0,X1] : (~l1_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | r2_hidden(X0,u1_struct_0(X1)) | v2_struct_0(X1)) )),
% 0.18/0.43    inference(resolution,[],[f63,f56])).
% 0.18/0.43  fof(f56,plain,(
% 0.18/0.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f22])).
% 0.18/0.43  fof(f22,plain,(
% 0.18/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.43    inference(flattening,[],[f21])).
% 0.18/0.43  fof(f21,plain,(
% 0.18/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.18/0.43    inference(ennf_transformation,[],[f5])).
% 0.18/0.43  fof(f5,axiom,(
% 0.18/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.18/0.43  fof(f63,plain,(
% 0.18/0.43    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f31])).
% 0.18/0.43  fof(f31,plain,(
% 0.18/0.43    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.18/0.43    inference(flattening,[],[f30])).
% 0.18/0.43  fof(f30,plain,(
% 0.18/0.43    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.18/0.43    inference(ennf_transformation,[],[f2])).
% 0.18/0.43  fof(f2,axiom,(
% 0.18/0.43    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.18/0.43  % SZS output end Proof for theBenchmark
% 0.18/0.43  % (8784)------------------------------
% 0.18/0.43  % (8784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.43  % (8784)Termination reason: Refutation
% 0.18/0.43  
% 0.18/0.43  % (8784)Memory used [KB]: 6268
% 0.18/0.43  % (8784)Time elapsed: 0.064 s
% 0.18/0.43  % (8784)------------------------------
% 0.18/0.43  % (8784)------------------------------
% 0.18/0.44  % (8778)Success in time 0.102 s
%------------------------------------------------------------------------------
