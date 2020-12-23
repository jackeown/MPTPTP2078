%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 886 expanded)
%              Number of leaves         :   13 ( 362 expanded)
%              Depth                    :   30
%              Number of atoms          :  401 (6648 expanded)
%              Number of equality atoms :   73 (1720 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(global_subsumption,[],[f64,f274])).

fof(f274,plain,(
    sP0(sK4,sK3) ),
    inference(resolution,[],[f273,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK6(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK6(X0,X1)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK6(X0,X1),X0)
          & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK7(X0,X1,X4)) = X4
              & v3_pre_topc(sK7(X0,X1,X4),X1)
              & m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f25,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK6(X0,X1)
            | ~ v3_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK6(X0,X1),X0)
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK7(X0,X1,X4)) = X4
        & v3_pre_topc(sK7(X0,X1,X4),X1)
        & m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v3_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f273,plain,(
    ~ r1_tarski(sK6(sK4,sK3),sK4) ),
    inference(global_subsumption,[],[f64,f272])).

fof(f272,plain,
    ( ~ r1_tarski(sK6(sK4,sK3),sK4)
    | sP0(sK4,sK3) ),
    inference(resolution,[],[f271,f110])).

fof(f110,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
      | sP0(X0,sK3) ) ),
    inference(superposition,[],[f45,f100])).

fof(f100,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(global_subsumption,[],[f29,f99])).

fof(f99,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f98,f37])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f98,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | u1_struct_0(sK3) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f49,f33])).

fof(f33,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v2_tex_2(sK5,sK3)
    & v2_tex_2(sK4,sK2)
    & sK4 = sK5
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK3)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f8,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tex_2(X3,X1)
                    & v2_tex_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,sK2)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tex_2(X3,X1)
                & v2_tex_2(X2,sK2)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tex_2(X3,sK3)
              & v2_tex_2(X2,sK2)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tex_2(X3,sK3)
            & v2_tex_2(X2,sK2)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X3] :
          ( ~ v2_tex_2(X3,sK3)
          & v2_tex_2(sK4,sK2)
          & sK4 = X3
          & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ v2_tex_2(X3,sK3)
        & v2_tex_2(sK4,sK2)
        & sK4 = X3
        & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ~ v2_tex_2(sK5,sK3)
      & v2_tex_2(sK4,sK2)
      & sK4 = sK5
      & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tex_2)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f29,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f271,plain,
    ( ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK6(sK4,sK3),sK4) ),
    inference(global_subsumption,[],[f59,f64,f270])).

fof(f270,plain,
    ( ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ sP0(sK4,sK2)
    | sP0(sK4,sK3) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,
    ( ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ sP0(sK4,sK2)
    | sP0(sK4,sK3) ),
    inference(resolution,[],[f268,f166])).

fof(f166,plain,(
    ! [X4,X5] :
      ( v3_pre_topc(sK7(X5,sK2,sK6(X4,sK3)),sK2)
      | ~ r1_tarski(sK6(X4,sK3),X5)
      | ~ sP0(X5,sK2)
      | sP0(X4,sK3) ) ),
    inference(resolution,[],[f43,f110])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | v3_pre_topc(sK7(X0,X1,X4),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f268,plain,
    ( ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK2)
    | ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK6(sK4,sK3),sK4) ),
    inference(global_subsumption,[],[f59,f267])).

fof(f267,plain,
    ( ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK4,sK2)
    | ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK2) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,
    ( ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK4,sK2)
    | ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK2)
    | ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f265,f245])).

fof(f245,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(sK7(X1,sK2,X0),sK3)
      | ~ sP0(X1,sK2)
      | ~ v3_pre_topc(sK7(X1,sK2,X0),sK2)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ sP0(X1,sK2)
      | ~ v3_pre_topc(sK7(X1,sK2,X0),sK2)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ sP0(X1,sK2)
      | ~ r1_tarski(X0,X1)
      | v3_pre_topc(sK7(X1,sK2,X0),sK3) ) ),
    inference(resolution,[],[f192,f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X1,sK2,X0),u1_pre_topc(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ sP0(X1,sK2)
      | ~ r1_tarski(X0,X1)
      | v3_pre_topc(sK7(X1,sK2,X0),sK3) ) ),
    inference(resolution,[],[f42,f143])).

fof(f143,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X1,u1_pre_topc(sK2))
      | v3_pre_topc(X1,sK3) ) ),
    inference(backward_demodulation,[],[f105,f136])).

fof(f136,plain,(
    u1_pre_topc(sK2) = u1_pre_topc(sK3) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | u1_pre_topc(sK3) = X1 ) ),
    inference(subsumption_resolution,[],[f108,f112])).

fof(f112,plain,(
    m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(global_subsumption,[],[f30,f111])).

fof(f111,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK3) ),
    inference(superposition,[],[f37,f100])).

fof(f30,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | u1_pre_topc(sK3) = X1 ) ),
    inference(backward_demodulation,[],[f94,f100])).

fof(f94,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | u1_pre_topc(sK3) = X1
      | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ) ),
    inference(superposition,[],[f50,f33])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f105,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X1,u1_pre_topc(sK3))
      | v3_pre_topc(X1,sK3) ) ),
    inference(backward_demodulation,[],[f80,f100])).

fof(f80,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r2_hidden(X1,u1_pre_topc(sK3))
      | v3_pre_topc(X1,sK3) ) ),
    inference(resolution,[],[f39,f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f192,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK7(X9,sK2,X8),u1_pre_topc(sK2))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ sP0(X9,sK2)
      | ~ v3_pre_topc(sK7(X9,sK2,X8),sK2)
      | ~ r1_tarski(X8,X9) ) ),
    inference(resolution,[],[f42,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X0,sK2)
      | r2_hidden(X0,u1_pre_topc(sK2)) ) ),
    inference(resolution,[],[f38,f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f265,plain,
    ( ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3)
    | ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_subsumption,[],[f59,f264])).

fof(f264,plain,
    ( ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3)
    | ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK4,sK2) ),
    inference(resolution,[],[f263,f42])).

% (31618)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f263,plain,
    ( ~ m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3) ),
    inference(global_subsumption,[],[f64,f262])).

fof(f262,plain,
    ( sP0(sK4,sK3)
    | ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3)
    | ~ m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(trivial_inequality_removal,[],[f261])).

fof(f261,plain,
    ( sK6(sK4,sK3) != sK6(sK4,sK3)
    | sP0(sK4,sK3)
    | ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3)
    | ~ m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(superposition,[],[f221,f259])).

fof(f259,plain,(
    sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3))) ),
    inference(global_subsumption,[],[f64,f258])).

fof(f258,plain,
    ( sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3)))
    | sP0(sK4,sK3) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3)))
    | sP0(sK4,sK3)
    | sP0(sK4,sK3) ),
    inference(resolution,[],[f252,f46])).

fof(f252,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK6(X0,sK3),sK4)
      | sK6(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(X0,sK3)))
      | sP0(X0,sK3) ) ),
    inference(resolution,[],[f224,f59])).

fof(f224,plain,(
    ! [X4,X5] :
      ( ~ sP0(X5,sK2)
      | sK6(X4,sK3) = k9_subset_1(u1_struct_0(sK2),X5,sK7(X5,sK2,sK6(X4,sK3)))
      | ~ r1_tarski(sK6(X4,sK3),X5)
      | sP0(X4,sK3) ) ),
    inference(resolution,[],[f44,f110])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | k9_subset_1(u1_struct_0(X1),X0,sK7(X0,X1,X4)) = X4
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f221,plain,(
    ! [X0,X1] :
      ( sK6(X0,sK3) != k9_subset_1(u1_struct_0(sK2),X0,X1)
      | sP0(X0,sK3)
      | ~ v3_pre_topc(X1,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(superposition,[],[f47,f100])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK6(X0,X1)
      | sP0(X0,X1)
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    sP0(sK4,sK2) ),
    inference(global_subsumption,[],[f35,f58])).

fof(f58,plain,
    ( ~ v2_tex_2(sK4,sK2)
    | sP0(sK4,sK2) ),
    inference(resolution,[],[f55,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f55,plain,(
    sP1(sK2,sK4) ),
    inference(resolution,[],[f53,f31])).

fof(f31,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f48,f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f15,f14])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f35,plain,(
    v2_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ~ sP0(sK4,sK3) ),
    inference(global_subsumption,[],[f51,f62])).

fof(f62,plain,
    ( ~ sP0(sK4,sK3)
    | v2_tex_2(sK4,sK3) ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    sP1(sK3,sK4) ),
    inference(resolution,[],[f54,f52])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f32,f34])).

fof(f34,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | sP1(sK3,X1) ) ),
    inference(resolution,[],[f48,f30])).

fof(f51,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(backward_demodulation,[],[f36,f34])).

fof(f36,plain,(
    ~ v2_tex_2(sK5,sK3) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (31628)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.47  % (31628)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (31636)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f275,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(global_subsumption,[],[f64,f274])).
% 0.20/0.48  fof(f274,plain,(
% 0.20/0.48    sP0(sK4,sK3)),
% 0.20/0.48    inference(resolution,[],[f273,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(sK6(X0,X1),X0) | sP0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK6(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK6(X0,X1),X0) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK7(X0,X1,X4)) = X4 & v3_pre_topc(sK7(X0,X1,X4),X1) & m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f25,f27,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK6(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK6(X0,X1),X0) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK7(X0,X1,X4)) = X4 & v3_pre_topc(sK7(X0,X1,X4),X1) & m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    ~r1_tarski(sK6(sK4,sK3),sK4)),
% 0.20/0.49    inference(global_subsumption,[],[f64,f272])).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    ~r1_tarski(sK6(sK4,sK3),sK4) | sP0(sK4,sK3)),
% 0.20/0.49    inference(resolution,[],[f271,f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK6(X0,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | sP0(X0,sK3)) )),
% 0.20/0.49    inference(superposition,[],[f45,f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.20/0.49    inference(global_subsumption,[],[f29,f99])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    u1_struct_0(sK2) = u1_struct_0(sK3) | ~l1_pre_topc(sK2)),
% 0.20/0.49    inference(resolution,[],[f98,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.20/0.49    inference(equality_resolution,[],[f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | u1_struct_0(sK3) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.49    inference(superposition,[],[f49,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    (((~v2_tex_2(sK5,sK3) & v2_tex_2(sK4,sK2) & sK4 = sK5 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK3)) & l1_pre_topc(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f8,f20,f19,f18,f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,sK2) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(X1)) & l1_pre_topc(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,sK2) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v2_tex_2(X3,sK3) & v2_tex_2(X2,sK2) & X2 = X3 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X2] : (? [X3] : (~v2_tex_2(X3,sK3) & v2_tex_2(X2,sK2) & X2 = X3 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) => (? [X3] : (~v2_tex_2(X3,sK3) & v2_tex_2(sK4,sK2) & sK4 = X3 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X3] : (~v2_tex_2(X3,sK3) & v2_tex_2(sK4,sK2) & sK4 = X3 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) => (~v2_tex_2(sK5,sK3) & v2_tex_2(sK4,sK2) & sK4 = sK5 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tex_2(X3,X1) & (v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f5])).
% 0.20/0.49  fof(f5,conjecture,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tex_2)).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    l1_pre_topc(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK6(sK4,sK3),sK4)),
% 0.20/0.49    inference(global_subsumption,[],[f59,f64,f270])).
% 0.20/0.49  fof(f270,plain,(
% 0.20/0.49    ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK6(sK4,sK3),sK4) | ~sP0(sK4,sK2) | sP0(sK4,sK3)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f269])).
% 0.20/0.49  fof(f269,plain,(
% 0.20/0.49    ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK6(sK4,sK3),sK4) | ~r1_tarski(sK6(sK4,sK3),sK4) | ~sP0(sK4,sK2) | sP0(sK4,sK3)),
% 0.20/0.49    inference(resolution,[],[f268,f166])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ( ! [X4,X5] : (v3_pre_topc(sK7(X5,sK2,sK6(X4,sK3)),sK2) | ~r1_tarski(sK6(X4,sK3),X5) | ~sP0(X5,sK2) | sP0(X4,sK3)) )),
% 0.20/0.49    inference(resolution,[],[f43,f110])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,X0) | v3_pre_topc(sK7(X0,X1,X4),X1) | ~sP0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK2) | ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK6(sK4,sK3),sK4)),
% 0.20/0.49    inference(global_subsumption,[],[f59,f267])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    ~r1_tarski(sK6(sK4,sK3),sK4) | ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK4,sK2) | ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK2)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f266])).
% 0.20/0.49  fof(f266,plain,(
% 0.20/0.49    ~r1_tarski(sK6(sK4,sK3),sK4) | ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK4,sK2) | ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK2) | ~r1_tarski(sK6(sK4,sK3),sK4) | ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.49    inference(resolution,[],[f265,f245])).
% 0.20/0.49  fof(f245,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v3_pre_topc(sK7(X1,sK2,X0),sK3) | ~sP0(X1,sK2) | ~v3_pre_topc(sK7(X1,sK2,X0),sK2) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f244])).
% 0.20/0.49  fof(f244,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(X1,sK2) | ~v3_pre_topc(sK7(X1,sK2,X0),sK2) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(X1,sK2) | ~r1_tarski(X0,X1) | v3_pre_topc(sK7(X1,sK2,X0),sK3)) )),
% 0.20/0.49    inference(resolution,[],[f192,f188])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(sK7(X1,sK2,X0),u1_pre_topc(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(X1,sK2) | ~r1_tarski(X0,X1) | v3_pre_topc(sK7(X1,sK2,X0),sK3)) )),
% 0.20/0.49    inference(resolution,[],[f42,f143])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X1,u1_pre_topc(sK2)) | v3_pre_topc(X1,sK3)) )),
% 0.20/0.49    inference(backward_demodulation,[],[f105,f136])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    u1_pre_topc(sK2) = u1_pre_topc(sK3)),
% 0.20/0.49    inference(equality_resolution,[],[f113])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | u1_pre_topc(sK3) = X1) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f108,f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.49    inference(global_subsumption,[],[f30,f111])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~l1_pre_topc(sK3)),
% 0.20/0.49    inference(superposition,[],[f37,f100])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    l1_pre_topc(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | u1_pre_topc(sK3) = X1) )),
% 0.20/0.49    inference(backward_demodulation,[],[f94,f100])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) | u1_pre_topc(sK3) = X1 | ~m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) )),
% 0.20/0.49    inference(superposition,[],[f50,f33])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X1,u1_pre_topc(sK3)) | v3_pre_topc(X1,sK3)) )),
% 0.20/0.49    inference(backward_demodulation,[],[f80,f100])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(X1,u1_pre_topc(sK3)) | v3_pre_topc(X1,sK3)) )),
% 0.20/0.49    inference(resolution,[],[f39,f30])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    ( ! [X8,X9] : (r2_hidden(sK7(X9,sK2,X8),u1_pre_topc(sK2)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(X9,sK2) | ~v3_pre_topc(sK7(X9,sK2,X8),sK2) | ~r1_tarski(X8,X9)) )),
% 0.20/0.49    inference(resolution,[],[f42,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X0,sK2) | r2_hidden(X0,u1_pre_topc(sK2))) )),
% 0.20/0.49    inference(resolution,[],[f38,f29])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f265,plain,(
% 0.20/0.49    ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3) | ~r1_tarski(sK6(sK4,sK3),sK4) | ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.49    inference(global_subsumption,[],[f59,f264])).
% 0.20/0.49  fof(f264,plain,(
% 0.20/0.49    ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3) | ~r1_tarski(sK6(sK4,sK3),sK4) | ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK4,sK2)),
% 0.20/0.49    inference(resolution,[],[f263,f42])).
% 0.20/0.49  % (31618)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  fof(f263,plain,(
% 0.20/0.49    ~m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3)),
% 0.20/0.49    inference(global_subsumption,[],[f64,f262])).
% 0.20/0.49  fof(f262,plain,(
% 0.20/0.49    sP0(sK4,sK3) | ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3) | ~m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f261])).
% 0.20/0.49  fof(f261,plain,(
% 0.20/0.49    sK6(sK4,sK3) != sK6(sK4,sK3) | sP0(sK4,sK3) | ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3) | ~m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.49    inference(superposition,[],[f221,f259])).
% 0.20/0.49  fof(f259,plain,(
% 0.20/0.49    sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3)))),
% 0.20/0.49    inference(global_subsumption,[],[f64,f258])).
% 0.20/0.49  fof(f258,plain,(
% 0.20/0.49    sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3))) | sP0(sK4,sK3)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f257])).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3))) | sP0(sK4,sK3) | sP0(sK4,sK3)),
% 0.20/0.49    inference(resolution,[],[f252,f46])).
% 0.20/0.49  fof(f252,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(sK6(X0,sK3),sK4) | sK6(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(X0,sK3))) | sP0(X0,sK3)) )),
% 0.20/0.49    inference(resolution,[],[f224,f59])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    ( ! [X4,X5] : (~sP0(X5,sK2) | sK6(X4,sK3) = k9_subset_1(u1_struct_0(sK2),X5,sK7(X5,sK2,sK6(X4,sK3))) | ~r1_tarski(sK6(X4,sK3),X5) | sP0(X4,sK3)) )),
% 0.20/0.49    inference(resolution,[],[f44,f110])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,X0) | k9_subset_1(u1_struct_0(X1),X0,sK7(X0,X1,X4)) = X4 | ~sP0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sK6(X0,sK3) != k9_subset_1(u1_struct_0(sK2),X0,X1) | sP0(X0,sK3) | ~v3_pre_topc(X1,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.49    inference(superposition,[],[f47,f100])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK6(X0,X1) | sP0(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    sP0(sK4,sK2)),
% 0.20/0.49    inference(global_subsumption,[],[f35,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ~v2_tex_2(sK4,sK2) | sP0(sK4,sK2)),
% 0.20/0.49    inference(resolution,[],[f55,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    sP1(sK2,sK4)),
% 0.20/0.49    inference(resolution,[],[f53,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 0.20/0.49    inference(resolution,[],[f48,f29])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(definition_folding,[],[f12,f15,f14])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    v2_tex_2(sK4,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ~sP0(sK4,sK3)),
% 0.20/0.49    inference(global_subsumption,[],[f51,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ~sP0(sK4,sK3) | v2_tex_2(sK4,sK3)),
% 0.20/0.49    inference(resolution,[],[f60,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    sP1(sK3,sK4)),
% 0.20/0.49    inference(resolution,[],[f54,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.49    inference(forward_demodulation,[],[f32,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    sK4 = sK5),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | sP1(sK3,X1)) )),
% 0.20/0.49    inference(resolution,[],[f48,f30])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ~v2_tex_2(sK4,sK3)),
% 0.20/0.49    inference(backward_demodulation,[],[f36,f34])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ~v2_tex_2(sK5,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (31628)------------------------------
% 0.20/0.49  % (31628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31628)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (31628)Memory used [KB]: 6524
% 0.20/0.49  % (31628)Time elapsed: 0.057 s
% 0.20/0.49  % (31628)------------------------------
% 0.20/0.49  % (31628)------------------------------
% 0.20/0.49  % (31615)Success in time 0.134 s
%------------------------------------------------------------------------------
