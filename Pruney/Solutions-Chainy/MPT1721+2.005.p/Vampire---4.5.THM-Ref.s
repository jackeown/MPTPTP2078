%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 373 expanded)
%              Number of leaves         :   42 ( 186 expanded)
%              Depth                    :   11
%              Number of atoms          :  800 (2834 expanded)
%              Number of equality atoms :   60 (  74 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f457,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f94,f98,f102,f106,f110,f114,f118,f122,f131,f140,f158,f175,f206,f212,f273,f291,f340,f348,f349,f384,f449,f452,f456])).

fof(f456,plain,
    ( ~ spl7_48
    | spl7_20 ),
    inference(avatar_split_clause,[],[f455,f170,f338])).

fof(f338,plain,
    ( spl7_48
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f170,plain,
    ( spl7_20
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f455,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_20 ),
    inference(resolution,[],[f171,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f171,plain,
    ( ~ l1_struct_0(sK3)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f452,plain,
    ( spl7_6
    | ~ spl7_48
    | spl7_10
    | ~ spl7_4
    | spl7_8
    | ~ spl7_3
    | spl7_72 ),
    inference(avatar_split_clause,[],[f450,f447,f80,f100,f84,f108,f338,f92])).

fof(f92,plain,
    ( spl7_6
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f108,plain,
    ( spl7_10
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f84,plain,
    ( spl7_4
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f100,plain,
    ( spl7_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f80,plain,
    ( spl7_3
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f447,plain,
    ( spl7_72
  <=> m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f450,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl7_72 ),
    inference(resolution,[],[f448,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (22513)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f448,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3)
    | spl7_72 ),
    inference(avatar_component_clause,[],[f447])).

fof(f449,plain,
    ( ~ spl7_48
    | ~ spl7_38
    | ~ spl7_72
    | spl7_56 ),
    inference(avatar_split_clause,[],[f445,f382,f447,f293,f338])).

fof(f293,plain,
    ( spl7_38
  <=> l1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f382,plain,
    ( spl7_56
  <=> r1_tarski(k2_struct_0(k2_tsep_1(sK3,sK1,sK2)),k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f445,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3)
    | ~ l1_pre_topc(k2_tsep_1(sK3,sK1,sK2))
    | ~ l1_pre_topc(sK3)
    | spl7_56 ),
    inference(resolution,[],[f383,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
                & ( ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
                    & r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
                    & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
                          & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
                          & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,u1_pre_topc(X1)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                & r2_hidden(X4,u1_pre_topc(X0))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,u1_pre_topc(X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X0))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X0))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
          & r2_hidden(X7,u1_pre_topc(X0))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X4] :
                        ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                        & r2_hidden(X4,u1_pre_topc(X0))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X7] :
                            ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
                            & r2_hidden(X7,u1_pre_topc(X0))
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

% (22511)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f383,plain,
    ( ~ r1_tarski(k2_struct_0(k2_tsep_1(sK3,sK1,sK2)),k2_struct_0(sK3))
    | spl7_56 ),
    inference(avatar_component_clause,[],[f382])).

fof(f384,plain,
    ( ~ spl7_56
    | spl7_21
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f366,f288,f173,f382])).

fof(f173,plain,
    ( spl7_21
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f288,plain,
    ( spl7_37
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k2_struct_0(k2_tsep_1(sK3,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f366,plain,
    ( ~ r1_tarski(k2_struct_0(k2_tsep_1(sK3,sK1,sK2)),k2_struct_0(sK3))
    | spl7_21
    | ~ spl7_37 ),
    inference(superposition,[],[f174,f289])).

fof(f289,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k2_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f288])).

fof(f174,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k2_struct_0(sK3))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f173])).

fof(f349,plain,
    ( ~ spl7_38
    | spl7_36 ),
    inference(avatar_split_clause,[],[f330,f285,f293])).

fof(f285,plain,
    ( spl7_36
  <=> l1_struct_0(k2_tsep_1(sK3,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f330,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK3,sK1,sK2))
    | spl7_36 ),
    inference(resolution,[],[f286,f50])).

fof(f286,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | spl7_36 ),
    inference(avatar_component_clause,[],[f285])).

fof(f348,plain,
    ( ~ spl7_11
    | ~ spl7_5
    | spl7_48 ),
    inference(avatar_split_clause,[],[f343,f338,f88,f112])).

fof(f112,plain,
    ( spl7_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f88,plain,
    ( spl7_5
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f343,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_5
    | spl7_48 ),
    inference(resolution,[],[f341,f89])).

fof(f89,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_48 ),
    inference(resolution,[],[f339,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f339,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_48 ),
    inference(avatar_component_clause,[],[f338])).

fof(f340,plain,
    ( spl7_6
    | spl7_10
    | ~ spl7_4
    | spl7_8
    | ~ spl7_3
    | ~ spl7_48
    | spl7_38 ),
    inference(avatar_split_clause,[],[f335,f293,f338,f80,f100,f84,f108,f92])).

fof(f335,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | spl7_38 ),
    inference(duplicate_literal_removal,[],[f333])).

fof(f333,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl7_38 ),
    inference(resolution,[],[f331,f68])).

fof(f331,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0)
        | ~ l1_pre_topc(X0) )
    | spl7_38 ),
    inference(resolution,[],[f294,f61])).

fof(f294,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK3,sK1,sK2))
    | spl7_38 ),
    inference(avatar_component_clause,[],[f293])).

fof(f291,plain,
    ( ~ spl7_36
    | spl7_37
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f275,f270,f288,f285])).

fof(f270,plain,
    ( spl7_35
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f275,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k2_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | ~ l1_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | ~ spl7_35 ),
    inference(superposition,[],[f49,f271])).

fof(f271,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f270])).

fof(f49,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f273,plain,
    ( spl7_6
    | ~ spl7_5
    | spl7_35
    | ~ spl7_4
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f262,f210,f204,f112,f80,f84,f270,f88,f92])).

fof(f204,plain,
    ( spl7_25
  <=> ! [X0] :
        ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f210,plain,
    ( spl7_26
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f262,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(resolution,[],[f258,f81])).

fof(f81,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f258,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl7_11
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f256,f211])).

fof(f211,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f210])).

fof(f256,plain,
    ( ! [X0] :
        ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl7_11
    | ~ spl7_25 ),
    inference(resolution,[],[f208,f113])).

fof(f113,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0) )
    | ~ spl7_25 ),
    inference(resolution,[],[f205,f61])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f204])).

fof(f212,plain,
    ( ~ spl7_7
    | ~ spl7_9
    | spl7_26
    | spl7_13
    | ~ spl7_11
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f207,f204,f112,f120,f210,f104,f96])).

fof(f96,plain,
    ( spl7_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f104,plain,
    ( spl7_9
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f120,plain,
    ( spl7_13
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f207,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl7_11
    | ~ spl7_25 ),
    inference(resolution,[],[f205,f113])).

fof(f206,plain,
    ( spl7_10
    | spl7_8
    | spl7_25
    | spl7_2 ),
    inference(avatar_split_clause,[],[f202,f76,f204,f100,f108])).

fof(f76,plain,
    ( spl7_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f202,plain,
    ( ! [X0] :
        ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2))
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl7_2 ),
    inference(resolution,[],[f125,f77])).

fof(f77,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f124,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f123,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f70,f68])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f175,plain,
    ( ~ spl7_20
    | ~ spl7_21
    | spl7_16 ),
    inference(avatar_split_clause,[],[f161,f138,f173,f170])).

fof(f138,plain,
    ( spl7_16
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f161,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k2_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | spl7_16 ),
    inference(superposition,[],[f139,f49])).

fof(f139,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f158,plain,
    ( spl7_13
    | ~ spl7_11
    | spl7_10
    | ~ spl7_9
    | spl7_8
    | ~ spl7_7
    | spl7_15 ),
    inference(avatar_split_clause,[],[f152,f135,f96,f100,f104,f108,f112,f120])).

fof(f135,plain,
    ( spl7_15
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f152,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl7_15 ),
    inference(resolution,[],[f68,f136])).

fof(f136,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f140,plain,
    ( ~ spl7_5
    | ~ spl7_15
    | ~ spl7_16
    | spl7_1
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f132,f129,f72,f138,f135,f88])).

fof(f72,plain,
    ( spl7_1
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f129,plain,
    ( spl7_14
  <=> ! [X1,X0] :
        ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
        | m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f132,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | spl7_1
    | ~ spl7_14 ),
    inference(resolution,[],[f130,f73])).

fof(f73,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(X0,X1)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f131,plain,
    ( ~ spl7_11
    | spl7_14
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f126,f116,f129,f112])).

fof(f116,plain,
    ( spl7_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | m1_pre_topc(X0,X1) )
    | ~ spl7_12 ),
    inference(resolution,[],[f64,f117])).

fof(f117,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f122,plain,(
    ~ spl7_13 ),
    inference(avatar_split_clause,[],[f36,f120])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3)
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3)
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(sK1,X3)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3)
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X2,X3)
            & m1_pre_topc(sK1,X3)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3)
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(sK2,X3)
          & m1_pre_topc(sK1,X3)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3)
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(sK2,X3)
        & m1_pre_topc(sK1,X3)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK3)
      & m1_pre_topc(sK1,sK3)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).

fof(f118,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f37,f116])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f114,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f38,f112])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f110,plain,(
    ~ spl7_10 ),
    inference(avatar_split_clause,[],[f39,f108])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

% (22508)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f106,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f40,f104])).

fof(f40,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f102,plain,(
    ~ spl7_8 ),
    inference(avatar_split_clause,[],[f41,f100])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f42,f96])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f43,f92])).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f44,f88])).

fof(f44,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f26])).

% (22505)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f82,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f46,f80])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f47,f76])).

fof(f47,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f48,f72])).

fof(f48,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:46:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (22521)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (22521)Refutation not found, incomplete strategy% (22521)------------------------------
% 0.22/0.48  % (22521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22515)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (22506)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (22516)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (22501)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (22507)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (22521)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22521)Memory used [KB]: 10618
% 0.22/0.49  % (22521)Time elapsed: 0.035 s
% 0.22/0.49  % (22521)------------------------------
% 0.22/0.49  % (22521)------------------------------
% 0.22/0.49  % (22502)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (22503)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (22518)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (22504)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (22507)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (22514)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (22520)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (22517)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f457,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f94,f98,f102,f106,f110,f114,f118,f122,f131,f140,f158,f175,f206,f212,f273,f291,f340,f348,f349,f384,f449,f452,f456])).
% 0.22/0.50  fof(f456,plain,(
% 0.22/0.50    ~spl7_48 | spl7_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f455,f170,f338])).
% 0.22/0.50  fof(f338,plain,(
% 0.22/0.50    spl7_48 <=> l1_pre_topc(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    spl7_20 <=> l1_struct_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.22/0.50  fof(f455,plain,(
% 0.22/0.50    ~l1_pre_topc(sK3) | spl7_20),
% 0.22/0.50    inference(resolution,[],[f171,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ~l1_struct_0(sK3) | spl7_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f170])).
% 0.22/0.50  fof(f452,plain,(
% 0.22/0.50    spl7_6 | ~spl7_48 | spl7_10 | ~spl7_4 | spl7_8 | ~spl7_3 | spl7_72),
% 0.22/0.50    inference(avatar_split_clause,[],[f450,f447,f80,f100,f84,f108,f338,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl7_6 <=> v2_struct_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl7_10 <=> v2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl7_4 <=> m1_pre_topc(sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    spl7_8 <=> v2_struct_0(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl7_3 <=> m1_pre_topc(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.50  fof(f447,plain,(
% 0.22/0.50    spl7_72 <=> m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 0.22/0.50  fof(f450,plain,(
% 0.22/0.50    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | spl7_72),
% 0.22/0.50    inference(resolution,[],[f448,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  % (22513)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.22/0.50  fof(f448,plain,(
% 0.22/0.50    ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3) | spl7_72),
% 0.22/0.50    inference(avatar_component_clause,[],[f447])).
% 0.22/0.50  fof(f449,plain,(
% 0.22/0.50    ~spl7_48 | ~spl7_38 | ~spl7_72 | spl7_56),
% 0.22/0.50    inference(avatar_split_clause,[],[f445,f382,f447,f293,f338])).
% 0.22/0.50  fof(f293,plain,(
% 0.22/0.50    spl7_38 <=> l1_pre_topc(k2_tsep_1(sK3,sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.22/0.50  fof(f382,plain,(
% 0.22/0.50    spl7_56 <=> r1_tarski(k2_struct_0(k2_tsep_1(sK3,sK1,sK2)),k2_struct_0(sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 0.22/0.50  fof(f445,plain,(
% 0.22/0.50    ~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),sK3) | ~l1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) | ~l1_pre_topc(sK3) | spl7_56),
% 0.22/0.50    inference(resolution,[],[f383,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & ((sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) & r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) & r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(rectify,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f14])).
% 0.22/0.51  % (22511)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.22/0.51  fof(f383,plain,(
% 0.22/0.51    ~r1_tarski(k2_struct_0(k2_tsep_1(sK3,sK1,sK2)),k2_struct_0(sK3)) | spl7_56),
% 0.22/0.51    inference(avatar_component_clause,[],[f382])).
% 0.22/0.51  fof(f384,plain,(
% 0.22/0.51    ~spl7_56 | spl7_21 | ~spl7_37),
% 0.22/0.51    inference(avatar_split_clause,[],[f366,f288,f173,f382])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    spl7_21 <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k2_struct_0(sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    spl7_37 <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k2_struct_0(k2_tsep_1(sK3,sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.22/0.51  fof(f366,plain,(
% 0.22/0.51    ~r1_tarski(k2_struct_0(k2_tsep_1(sK3,sK1,sK2)),k2_struct_0(sK3)) | (spl7_21 | ~spl7_37)),
% 0.22/0.51    inference(superposition,[],[f174,f289])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k2_struct_0(k2_tsep_1(sK3,sK1,sK2)) | ~spl7_37),
% 0.22/0.51    inference(avatar_component_clause,[],[f288])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k2_struct_0(sK3)) | spl7_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f173])).
% 0.22/0.51  fof(f349,plain,(
% 0.22/0.51    ~spl7_38 | spl7_36),
% 0.22/0.51    inference(avatar_split_clause,[],[f330,f285,f293])).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    spl7_36 <=> l1_struct_0(k2_tsep_1(sK3,sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    ~l1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) | spl7_36),
% 0.22/0.51    inference(resolution,[],[f286,f50])).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    ~l1_struct_0(k2_tsep_1(sK3,sK1,sK2)) | spl7_36),
% 0.22/0.51    inference(avatar_component_clause,[],[f285])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    ~spl7_11 | ~spl7_5 | spl7_48),
% 0.22/0.51    inference(avatar_split_clause,[],[f343,f338,f88,f112])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    spl7_11 <=> l1_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    spl7_5 <=> m1_pre_topc(sK3,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.51  fof(f343,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | (~spl7_5 | spl7_48)),
% 0.22/0.51    inference(resolution,[],[f341,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK0) | ~spl7_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f88])).
% 0.22/0.51  fof(f341,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl7_48),
% 0.22/0.51    inference(resolution,[],[f339,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f339,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | spl7_48),
% 0.22/0.51    inference(avatar_component_clause,[],[f338])).
% 0.22/0.51  fof(f340,plain,(
% 0.22/0.51    spl7_6 | spl7_10 | ~spl7_4 | spl7_8 | ~spl7_3 | ~spl7_48 | spl7_38),
% 0.22/0.51    inference(avatar_split_clause,[],[f335,f293,f338,f80,f100,f84,f108,f92])).
% 0.22/0.51  fof(f335,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK1) | v2_struct_0(sK3) | spl7_38),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f333])).
% 0.22/0.51  fof(f333,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | spl7_38),
% 0.22/0.51    inference(resolution,[],[f331,f68])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK3,sK1,sK2),X0) | ~l1_pre_topc(X0)) ) | spl7_38),
% 0.22/0.51    inference(resolution,[],[f294,f61])).
% 0.22/0.51  fof(f294,plain,(
% 0.22/0.51    ~l1_pre_topc(k2_tsep_1(sK3,sK1,sK2)) | spl7_38),
% 0.22/0.51    inference(avatar_component_clause,[],[f293])).
% 0.22/0.51  fof(f291,plain,(
% 0.22/0.51    ~spl7_36 | spl7_37 | ~spl7_35),
% 0.22/0.51    inference(avatar_split_clause,[],[f275,f270,f288,f285])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    spl7_35 <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k2_struct_0(k2_tsep_1(sK3,sK1,sK2)) | ~l1_struct_0(k2_tsep_1(sK3,sK1,sK2)) | ~spl7_35),
% 0.22/0.51    inference(superposition,[],[f49,f271])).
% 0.22/0.51  fof(f271,plain,(
% 0.22/0.51    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) | ~spl7_35),
% 0.22/0.51    inference(avatar_component_clause,[],[f270])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.51  fof(f273,plain,(
% 0.22/0.51    spl7_6 | ~spl7_5 | spl7_35 | ~spl7_4 | ~spl7_3 | ~spl7_11 | ~spl7_25 | ~spl7_26),
% 0.22/0.51    inference(avatar_split_clause,[],[f262,f210,f204,f112,f80,f84,f270,f88,f92])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    spl7_25 <=> ! [X0] : (k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    spl7_26 <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    ~m1_pre_topc(sK1,sK3) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(sK3,sK1,sK2)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | (~spl7_3 | ~spl7_11 | ~spl7_25 | ~spl7_26)),
% 0.22/0.51    inference(resolution,[],[f258,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK3) | ~spl7_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f80])).
% 0.22/0.51  fof(f258,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK1,X0) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (~spl7_11 | ~spl7_25 | ~spl7_26)),
% 0.22/0.51    inference(forward_demodulation,[],[f256,f211])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl7_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f210])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    ( ! [X0] : (k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (~spl7_11 | ~spl7_25)),
% 0.22/0.51    inference(resolution,[],[f208,f113])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    l1_pre_topc(sK0) | ~spl7_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f112])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X1) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0)) ) | ~spl7_25),
% 0.22/0.51    inference(resolution,[],[f205,f61])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK2,X0)) ) | ~spl7_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f204])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    ~spl7_7 | ~spl7_9 | spl7_26 | spl7_13 | ~spl7_11 | ~spl7_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f207,f204,f112,f120,f210,f104,f96])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    spl7_7 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    spl7_9 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    spl7_13 <=> v2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    v2_struct_0(sK0) | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK2,sK0) | (~spl7_11 | ~spl7_25)),
% 0.22/0.51    inference(resolution,[],[f205,f113])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    spl7_10 | spl7_8 | spl7_25 | spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f202,f76,f204,f100,f108])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    spl7_2 <=> r1_tsep_1(sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    ( ! [X0] : (k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(X0,sK1,sK2)) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | spl7_2),
% 0.22/0.51    inference(resolution,[],[f125,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ~r1_tsep_1(sK1,sK2) | spl7_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f76])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f124,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f123,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f70,f68])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    ~spl7_20 | ~spl7_21 | spl7_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f161,f138,f173,f170])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    spl7_16 <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k2_struct_0(sK3)) | ~l1_struct_0(sK3) | spl7_16),
% 0.22/0.51    inference(superposition,[],[f139,f49])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) | spl7_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f138])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    spl7_13 | ~spl7_11 | spl7_10 | ~spl7_9 | spl7_8 | ~spl7_7 | spl7_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f152,f135,f96,f100,f104,f108,f112,f120])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    spl7_15 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl7_15),
% 0.22/0.51    inference(resolution,[],[f68,f136])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | spl7_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f135])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ~spl7_5 | ~spl7_15 | ~spl7_16 | spl7_1 | ~spl7_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f132,f129,f72,f138,f135,f88])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    spl7_1 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl7_14 <=> ! [X1,X0] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ~r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK3)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | ~m1_pre_topc(sK3,sK0) | (spl7_1 | ~spl7_14)),
% 0.22/0.51    inference(resolution,[],[f130,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) | spl7_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f72])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0)) ) | ~spl7_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f129])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ~spl7_11 | spl7_14 | ~spl7_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f126,f116,f129,f112])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl7_12 <=> v2_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | m1_pre_topc(X0,X1)) ) | ~spl7_12),
% 0.22/0.51    inference(resolution,[],[f64,f117])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    v2_pre_topc(sK0) | ~spl7_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f116])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_pre_topc(X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ~spl7_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f36,f120])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    (((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f25,f24,f23,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    spl7_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f37,f116])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl7_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f38,f112])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ~spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f39,f108])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  % (22508)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    spl7_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f40,f104])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ~spl7_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f100])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ~v2_struct_0(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl7_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f42,f96])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ~spl7_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f43,f92])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ~v2_struct_0(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl7_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f44,f88])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl7_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f45,f84])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  % (22505)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    spl7_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f46,f80])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ~spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f47,f76])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~r1_tsep_1(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ~spl7_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f48,f72])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (22507)------------------------------
% 0.22/0.51  % (22507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22507)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (22507)Memory used [KB]: 11001
% 0.22/0.51  % (22507)Time elapsed: 0.045 s
% 0.22/0.51  % (22507)------------------------------
% 0.22/0.51  % (22507)------------------------------
% 0.22/0.51  % (22519)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (22500)Success in time 0.15 s
%------------------------------------------------------------------------------
