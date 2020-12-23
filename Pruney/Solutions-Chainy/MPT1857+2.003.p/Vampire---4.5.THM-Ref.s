%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 (1840 expanded)
%              Number of leaves         :   16 ( 758 expanded)
%              Depth                    :   30
%              Number of atoms          :  503 (14029 expanded)
%              Number of equality atoms :   66 (3514 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (22795)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f418,plain,(
    $false ),
    inference(global_subsumption,[],[f91,f417])).

% (22781)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f417,plain,(
    sP0(sK4,sK3) ),
    inference(resolution,[],[f416,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK6(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f33,f35,f34])).

fof(f34,plain,(
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

fof(f35,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK7(X0,X1,X4)) = X4
        & v3_pre_topc(sK7(X0,X1,X4),X1)
        & m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f416,plain,(
    ~ r1_tarski(sK6(sK4,sK3),sK4) ),
    inference(global_subsumption,[],[f91,f415])).

fof(f415,plain,
    ( ~ r1_tarski(sK6(sK4,sK3),sK4)
    | sP0(sK4,sK3) ),
    inference(resolution,[],[f414,f136])).

fof(f136,plain,(
    ! [X2] :
      ( m1_subset_1(sK6(X2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
      | sP0(X2,sK3) ) ),
    inference(superposition,[],[f57,f129])).

fof(f129,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(global_subsumption,[],[f40,f39,f71,f114,f126])).

fof(f126,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f121,f106])).

fof(f106,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(resolution,[],[f103,f102])).

fof(f102,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X1,sK3) ) ),
    inference(forward_demodulation,[],[f101,f43])).

fof(f43,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v2_tex_2(sK5,sK3)
    & v2_tex_2(sK4,sK2)
    & sK4 = sK5
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK3)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f28,f27,f26,f25])).

fof(f25,plain,
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

% (22802)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f26,plain,
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

fof(f27,plain,
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

fof(f28,plain,
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f101,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | m1_pre_topc(X1,sK3) ) ),
    inference(resolution,[],[f62,f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f103,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f48,f39])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | u1_struct_0(X0) = u1_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f119,f39])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f51,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

% (22781)Refutation not found, incomplete strategy% (22781)------------------------------
% (22781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22781)Termination reason: Refutation not found, incomplete strategy

% (22781)Memory used [KB]: 10618
% (22781)Time elapsed: 0.094 s
% (22781)------------------------------
% (22781)------------------------------
fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f114,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(global_subsumption,[],[f40,f111])).

fof(f111,plain,
    ( ~ l1_pre_topc(sK3)
    | m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f110,f72])).

fof(f72,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f47,f40])).

% (22787)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f47,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f110,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X1,sK2) ) ),
    inference(resolution,[],[f105,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X0,sK2) ) ),
    inference(resolution,[],[f62,f39])).

fof(f105,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(X1,sK3)
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f104,f43])).

fof(f104,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f48,f40])).

fof(f71,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f47,f39])).

fof(f39,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f414,plain,
    ( ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK6(sK4,sK3),sK4) ),
    inference(global_subsumption,[],[f86,f91,f413])).

fof(f413,plain,
    ( ~ sP0(sK4,sK2)
    | sP0(sK4,sK3)
    | ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(duplicate_literal_removal,[],[f410])).

fof(f410,plain,
    ( ~ sP0(sK4,sK2)
    | sP0(sK4,sK3)
    | ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f409,f283])).

fof(f283,plain,
    ( ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3)
    | ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_subsumption,[],[f86,f282])).

fof(f282,plain,
    ( ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3)
    | ~ r1_tarski(sK6(sK4,sK3),sK4)
    | ~ m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK4,sK2) ),
    inference(resolution,[],[f281,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f281,plain,
    ( ~ m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3) ),
    inference(global_subsumption,[],[f91,f280])).

fof(f280,plain,
    ( sP0(sK4,sK3)
    | ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3)
    | ~ m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(trivial_inequality_removal,[],[f279])).

fof(f279,plain,
    ( sK6(sK4,sK3) != sK6(sK4,sK3)
    | sP0(sK4,sK3)
    | ~ v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3)
    | ~ m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(superposition,[],[f228,f277])).

fof(f277,plain,(
    sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3))) ),
    inference(global_subsumption,[],[f91,f276])).

fof(f276,plain,
    ( sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3)))
    | sP0(sK4,sK3) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,
    ( sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3)))
    | sP0(sK4,sK3)
    | sP0(sK4,sK3) ),
    inference(resolution,[],[f270,f58])).

fof(f270,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK6(X0,sK3),sK4)
      | sK6(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(X0,sK3)))
      | sP0(X0,sK3) ) ),
    inference(resolution,[],[f233,f86])).

fof(f233,plain,(
    ! [X4,X5] :
      ( ~ sP0(X5,sK2)
      | sK6(X4,sK3) = k9_subset_1(u1_struct_0(sK2),X5,sK7(X5,sK2,sK6(X4,sK3)))
      | ~ r1_tarski(sK6(X4,sK3),X5)
      | sP0(X4,sK3) ) ),
    inference(resolution,[],[f56,f136])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | k9_subset_1(u1_struct_0(X1),X0,sK7(X0,X1,X4)) = X4
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

% (22788)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f228,plain,(
    ! [X0,X1] :
      ( sK6(X0,sK3) != k9_subset_1(u1_struct_0(sK2),X0,X1)
      | sP0(X0,sK3)
      | ~ v3_pre_topc(X1,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(superposition,[],[f59,f129])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK6(X0,X1)
      | sP0(X0,X1)
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f409,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(sK7(X1,sK2,sK6(X0,sK3)),sK3)
      | ~ sP0(X1,sK2)
      | sP0(X0,sK3)
      | ~ r1_tarski(sK6(X0,sK3),X1) ) ),
    inference(duplicate_literal_removal,[],[f408])).

fof(f408,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK6(X0,sK3),X1)
      | ~ sP0(X1,sK2)
      | sP0(X0,sK3)
      | v3_pre_topc(sK7(X1,sK2,sK6(X0,sK3)),sK3)
      | sP0(X0,sK3) ) ),
    inference(resolution,[],[f407,f136])).

fof(f407,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(X1,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(sK6(X1,sK3),X0)
      | ~ sP0(X0,sK2)
      | sP0(X1,sK3)
      | v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),sK3) ) ),
    inference(duplicate_literal_removal,[],[f406])).

fof(f406,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),sK3)
      | ~ r1_tarski(sK6(X1,sK3),X0)
      | ~ sP0(X0,sK2)
      | sP0(X1,sK3)
      | ~ r1_tarski(sK6(X1,sK3),X0)
      | ~ m1_subset_1(sK6(X1,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ sP0(X0,sK2) ) ),
    inference(resolution,[],[f399,f54])).

fof(f399,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK7(X0,sK2,sK6(X1,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),sK3)
      | ~ r1_tarski(sK6(X1,sK3),X0)
      | ~ sP0(X0,sK2)
      | sP0(X1,sK3) ) ),
    inference(global_subsumption,[],[f114,f397])).

fof(f397,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK7(X0,sK2,sK6(X1,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),sK3)
      | ~ r1_tarski(sK6(X1,sK3),X0)
      | ~ m1_pre_topc(sK3,sK2)
      | ~ sP0(X0,sK2)
      | sP0(X1,sK3) ) ),
    inference(superposition,[],[f395,f129])).

fof(f395,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,sK2,sK6(X1,sK3)),k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),X2)
      | ~ r1_tarski(sK6(X1,sK3),X0)
      | ~ m1_pre_topc(X2,sK2)
      | ~ sP0(X0,sK2)
      | sP0(X1,sK3) ) ),
    inference(duplicate_literal_removal,[],[f394])).

fof(f394,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,sK2,sK6(X1,sK3)),k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),X2)
      | ~ r1_tarski(sK6(X1,sK3),X0)
      | ~ m1_pre_topc(X2,sK2)
      | ~ sP0(X0,sK2)
      | sP0(X1,sK3)
      | sP0(X1,sK3) ) ),
    inference(resolution,[],[f310,f136])).

fof(f310,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(sK6(X4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK7(X3,sK2,sK6(X4,sK3)),k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(sK7(X3,sK2,sK6(X4,sK3)),X2)
      | ~ r1_tarski(sK6(X4,sK3),X3)
      | ~ m1_pre_topc(X2,sK2)
      | ~ sP0(X3,sK2)
      | sP0(X4,sK3) ) ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_pre_topc(X2,sK2)
      | ~ m1_subset_1(sK7(X3,sK2,sK6(X4,sK3)),k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(sK7(X3,sK2,sK6(X4,sK3)),X2)
      | ~ r1_tarski(sK6(X4,sK3),X3)
      | ~ m1_subset_1(sK6(X4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ sP0(X3,sK2)
      | ~ r1_tarski(sK6(X4,sK3),X3)
      | ~ sP0(X3,sK2)
      | sP0(X4,sK3) ) ),
    inference(resolution,[],[f264,f192])).

fof(f192,plain,(
    ! [X4,X5] :
      ( v3_pre_topc(sK7(X5,sK2,sK6(X4,sK3)),sK2)
      | ~ r1_tarski(sK6(X4,sK3),X5)
      | ~ sP0(X5,sK2)
      | sP0(X4,sK3) ) ),
    inference(resolution,[],[f55,f136])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | v3_pre_topc(sK7(X0,X1,X4),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f264,plain,(
    ! [X10,X8,X9] :
      ( ~ v3_pre_topc(sK7(X8,sK2,X9),sK2)
      | ~ m1_pre_topc(X10,sK2)
      | ~ m1_subset_1(sK7(X8,sK2,X9),k1_zfmisc_1(u1_struct_0(X10)))
      | v3_pre_topc(sK7(X8,sK2,X9),X10)
      | ~ r1_tarski(X9,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ sP0(X8,sK2) ) ),
    inference(resolution,[],[f253,f54])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f66,f39])).

fof(f66,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (22787)Refutation not found, incomplete strategy% (22787)------------------------------
% (22787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22787)Termination reason: Refutation not found, incomplete strategy

% (22787)Memory used [KB]: 10618
% (22787)Time elapsed: 0.061 s
% (22787)------------------------------
% (22787)------------------------------
fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f86,plain,(
    sP0(sK4,sK2) ),
    inference(global_subsumption,[],[f45,f85])).

fof(f85,plain,
    ( ~ v2_tex_2(sK4,sK2)
    | sP0(sK4,sK2) ),
    inference(resolution,[],[f82,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f82,plain,(
    sP1(sK2,sK4) ),
    inference(resolution,[],[f80,f41])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f60,f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f23,f22])).

% (22782)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f45,plain,(
    v2_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    ~ sP0(sK4,sK3) ),
    inference(global_subsumption,[],[f69,f89])).

fof(f89,plain,
    ( ~ sP0(sK4,sK3)
    | v2_tex_2(sK4,sK3) ),
    inference(resolution,[],[f87,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    sP1(sK3,sK4) ),
    inference(resolution,[],[f81,f70])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f42,f44])).

fof(f44,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
      | sP1(sK3,X1) ) ),
    inference(resolution,[],[f60,f40])).

fof(f69,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(backward_demodulation,[],[f46,f44])).

fof(f46,plain,(
    ~ v2_tex_2(sK5,sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:41:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (22801)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.47  % (22793)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (22785)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (22803)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (22786)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (22793)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  % (22795)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(global_subsumption,[],[f91,f417])).
% 0.22/0.51  % (22781)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  fof(f417,plain,(
% 0.22/0.51    sP0(sK4,sK3)),
% 0.22/0.51    inference(resolution,[],[f416,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(sK6(X0,X1),X0) | sP0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK6(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK6(X0,X1),X0) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK7(X0,X1,X4)) = X4 & v3_pre_topc(sK7(X0,X1,X4),X1) & m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f33,f35,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK6(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK6(X0,X1),X0) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK7(X0,X1,X4)) = X4 & v3_pre_topc(sK7(X0,X1,X4),X1) & m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f416,plain,(
% 0.22/0.51    ~r1_tarski(sK6(sK4,sK3),sK4)),
% 0.22/0.51    inference(global_subsumption,[],[f91,f415])).
% 0.22/0.51  fof(f415,plain,(
% 0.22/0.51    ~r1_tarski(sK6(sK4,sK3),sK4) | sP0(sK4,sK3)),
% 0.22/0.51    inference(resolution,[],[f414,f136])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X2] : (m1_subset_1(sK6(X2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | sP0(X2,sK3)) )),
% 0.22/0.51    inference(superposition,[],[f57,f129])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.22/0.51    inference(global_subsumption,[],[f40,f39,f71,f114,f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    u1_struct_0(sK2) = u1_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~m1_pre_topc(sK2,sK2)),
% 0.22/0.51    inference(resolution,[],[f121,f106])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f103,f102])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X1,sK3)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f101,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    (((~v2_tex_2(sK5,sK3) & v2_tex_2(sK4,sK2) & sK4 = sK5 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK3)) & l1_pre_topc(sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f28,f27,f26,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,sK2) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(X1)) & l1_pre_topc(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  % (22802)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,sK2) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v2_tex_2(X3,sK3) & v2_tex_2(X2,sK2) & X2 = X3 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ? [X2] : (? [X3] : (~v2_tex_2(X3,sK3) & v2_tex_2(X2,sK2) & X2 = X3 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) => (? [X3] : (~v2_tex_2(X3,sK3) & v2_tex_2(sK4,sK2) & sK4 = X3 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ? [X3] : (~v2_tex_2(X3,sK3) & v2_tex_2(sK4,sK2) & sK4 = X3 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) => (~v2_tex_2(sK5,sK3) & v2_tex_2(sK4,sK2) & sK4 = sK5 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tex_2(X3,X1) & v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tex_2(X3,X1) & (v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tex_2)).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | m1_pre_topc(X1,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f62,f40])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(resolution,[],[f48,f39])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(sK2,X0) | u1_struct_0(X0) = u1_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(resolution,[],[f119,f39])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X1) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(resolution,[],[f79,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X1) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f51,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f37])).
% 0.22/0.51  % (22781)Refutation not found, incomplete strategy% (22781)------------------------------
% 0.22/0.51  % (22781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22781)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22781)Memory used [KB]: 10618
% 0.22/0.51  % (22781)Time elapsed: 0.094 s
% 0.22/0.51  % (22781)------------------------------
% 0.22/0.51  % (22781)------------------------------
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK2)),
% 0.22/0.51    inference(global_subsumption,[],[f40,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | m1_pre_topc(sK3,sK2)),
% 0.22/0.51    inference(resolution,[],[f110,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK3)),
% 0.22/0.51    inference(resolution,[],[f47,f40])).
% 0.22/0.51  % (22787)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_pre_topc(X1,sK3) | ~l1_pre_topc(X1) | m1_pre_topc(X1,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f105,f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X0,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f62,f39])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ( ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(X1,sK3) | ~l1_pre_topc(X1)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f104,f43])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_pre_topc(X1,sK3) | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(X1)) )),
% 0.22/0.51    inference(resolution,[],[f48,f40])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK2)),
% 0.22/0.51    inference(resolution,[],[f47,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    l1_pre_topc(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    l1_pre_topc(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f414,plain,(
% 0.22/0.51    ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK6(sK4,sK3),sK4)),
% 0.22/0.51    inference(global_subsumption,[],[f86,f91,f413])).
% 0.22/0.51  fof(f413,plain,(
% 0.22/0.51    ~sP0(sK4,sK2) | sP0(sK4,sK3) | ~r1_tarski(sK6(sK4,sK3),sK4) | ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f410])).
% 0.22/0.51  fof(f410,plain,(
% 0.22/0.51    ~sP0(sK4,sK2) | sP0(sK4,sK3) | ~r1_tarski(sK6(sK4,sK3),sK4) | ~r1_tarski(sK6(sK4,sK3),sK4) | ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.51    inference(resolution,[],[f409,f283])).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3) | ~r1_tarski(sK6(sK4,sK3),sK4) | ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.51    inference(global_subsumption,[],[f86,f282])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3) | ~r1_tarski(sK6(sK4,sK3),sK4) | ~m1_subset_1(sK6(sK4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK4,sK2)),
% 0.22/0.51    inference(resolution,[],[f281,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X4,X0,X1] : (m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f281,plain,(
% 0.22/0.51    ~m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3)),
% 0.22/0.51    inference(global_subsumption,[],[f91,f280])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    sP0(sK4,sK3) | ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3) | ~m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f279])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    sK6(sK4,sK3) != sK6(sK4,sK3) | sP0(sK4,sK3) | ~v3_pre_topc(sK7(sK4,sK2,sK6(sK4,sK3)),sK3) | ~m1_subset_1(sK7(sK4,sK2,sK6(sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.51    inference(superposition,[],[f228,f277])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3)))),
% 0.22/0.51    inference(global_subsumption,[],[f91,f276])).
% 0.22/0.51  fof(f276,plain,(
% 0.22/0.51    sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3))) | sP0(sK4,sK3)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f275])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    sK6(sK4,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(sK4,sK3))) | sP0(sK4,sK3) | sP0(sK4,sK3)),
% 0.22/0.51    inference(resolution,[],[f270,f58])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(sK6(X0,sK3),sK4) | sK6(X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK4,sK7(sK4,sK2,sK6(X0,sK3))) | sP0(X0,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f233,f86])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~sP0(X5,sK2) | sK6(X4,sK3) = k9_subset_1(u1_struct_0(sK2),X5,sK7(X5,sK2,sK6(X4,sK3))) | ~r1_tarski(sK6(X4,sK3),X5) | sP0(X4,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f56,f136])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X4,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,X0) | k9_subset_1(u1_struct_0(X1),X0,sK7(X0,X1,X4)) = X4 | ~sP0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  % (22788)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK6(X0,sK3) != k9_subset_1(u1_struct_0(sK2),X0,X1) | sP0(X0,sK3) | ~v3_pre_topc(X1,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.22/0.51    inference(superposition,[],[f59,f129])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK6(X0,X1) | sP0(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f409,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v3_pre_topc(sK7(X1,sK2,sK6(X0,sK3)),sK3) | ~sP0(X1,sK2) | sP0(X0,sK3) | ~r1_tarski(sK6(X0,sK3),X1)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f408])).
% 0.22/0.51  fof(f408,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(sK6(X0,sK3),X1) | ~sP0(X1,sK2) | sP0(X0,sK3) | v3_pre_topc(sK7(X1,sK2,sK6(X0,sK3)),sK3) | sP0(X0,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f407,f136])).
% 0.22/0.51  fof(f407,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK6(X1,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK6(X1,sK3),X0) | ~sP0(X0,sK2) | sP0(X1,sK3) | v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),sK3)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f406])).
% 0.22/0.51  fof(f406,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),sK3) | ~r1_tarski(sK6(X1,sK3),X0) | ~sP0(X0,sK2) | sP0(X1,sK3) | ~r1_tarski(sK6(X1,sK3),X0) | ~m1_subset_1(sK6(X1,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(X0,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f399,f54])).
% 0.22/0.51  fof(f399,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK7(X0,sK2,sK6(X1,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),sK3) | ~r1_tarski(sK6(X1,sK3),X0) | ~sP0(X0,sK2) | sP0(X1,sK3)) )),
% 0.22/0.51    inference(global_subsumption,[],[f114,f397])).
% 0.22/0.51  fof(f397,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK7(X0,sK2,sK6(X1,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),sK3) | ~r1_tarski(sK6(X1,sK3),X0) | ~m1_pre_topc(sK3,sK2) | ~sP0(X0,sK2) | sP0(X1,sK3)) )),
% 0.22/0.51    inference(superposition,[],[f395,f129])).
% 0.22/0.51  fof(f395,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK7(X0,sK2,sK6(X1,sK3)),k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),X2) | ~r1_tarski(sK6(X1,sK3),X0) | ~m1_pre_topc(X2,sK2) | ~sP0(X0,sK2) | sP0(X1,sK3)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f394])).
% 0.22/0.51  fof(f394,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK7(X0,sK2,sK6(X1,sK3)),k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(sK7(X0,sK2,sK6(X1,sK3)),X2) | ~r1_tarski(sK6(X1,sK3),X0) | ~m1_pre_topc(X2,sK2) | ~sP0(X0,sK2) | sP0(X1,sK3) | sP0(X1,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f310,f136])).
% 0.22/0.51  fof(f310,plain,(
% 0.22/0.51    ( ! [X4,X2,X3] : (~m1_subset_1(sK6(X4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK7(X3,sK2,sK6(X4,sK3)),k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(sK7(X3,sK2,sK6(X4,sK3)),X2) | ~r1_tarski(sK6(X4,sK3),X3) | ~m1_pre_topc(X2,sK2) | ~sP0(X3,sK2) | sP0(X4,sK3)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f307])).
% 0.22/0.51  fof(f307,plain,(
% 0.22/0.51    ( ! [X4,X2,X3] : (~m1_pre_topc(X2,sK2) | ~m1_subset_1(sK7(X3,sK2,sK6(X4,sK3)),k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(sK7(X3,sK2,sK6(X4,sK3)),X2) | ~r1_tarski(sK6(X4,sK3),X3) | ~m1_subset_1(sK6(X4,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(X3,sK2) | ~r1_tarski(sK6(X4,sK3),X3) | ~sP0(X3,sK2) | sP0(X4,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f264,f192])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    ( ! [X4,X5] : (v3_pre_topc(sK7(X5,sK2,sK6(X4,sK3)),sK2) | ~r1_tarski(sK6(X4,sK3),X5) | ~sP0(X5,sK2) | sP0(X4,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f55,f136])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X4,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,X0) | v3_pre_topc(sK7(X0,X1,X4),X1) | ~sP0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f264,plain,(
% 0.22/0.51    ( ! [X10,X8,X9] : (~v3_pre_topc(sK7(X8,sK2,X9),sK2) | ~m1_pre_topc(X10,sK2) | ~m1_subset_1(sK7(X8,sK2,X9),k1_zfmisc_1(u1_struct_0(X10))) | v3_pre_topc(sK7(X8,sK2,X9),X10) | ~r1_tarski(X9,X8) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(X8,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f253,f54])).
% 0.22/0.51  fof(f253,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f66,f39])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X3,X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  % (22787)Refutation not found, incomplete strategy% (22787)------------------------------
% 0.22/0.51  % (22787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22787)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22787)Memory used [KB]: 10618
% 0.22/0.51  % (22787)Time elapsed: 0.061 s
% 0.22/0.51  % (22787)------------------------------
% 0.22/0.51  % (22787)------------------------------
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    sP0(sK4,sK2)),
% 0.22/0.51    inference(global_subsumption,[],[f45,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ~v2_tex_2(sK4,sK2) | sP0(sK4,sK2)),
% 0.22/0.51    inference(resolution,[],[f82,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    sP1(sK2,sK4)),
% 0.22/0.51    inference(resolution,[],[f80,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 0.22/0.51    inference(resolution,[],[f60,f39])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(definition_folding,[],[f18,f23,f22])).
% 0.22/0.51  % (22782)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    v2_tex_2(sK4,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ~sP0(sK4,sK3)),
% 0.22/0.51    inference(global_subsumption,[],[f69,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ~sP0(sK4,sK3) | v2_tex_2(sK4,sK3)),
% 0.22/0.51    inference(resolution,[],[f87,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tex_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    sP1(sK3,sK4)),
% 0.22/0.51    inference(resolution,[],[f81,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    inference(forward_demodulation,[],[f42,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    sK4 = sK5),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | sP1(sK3,X1)) )),
% 0.22/0.51    inference(resolution,[],[f60,f40])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ~v2_tex_2(sK4,sK3)),
% 0.22/0.51    inference(backward_demodulation,[],[f46,f44])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ~v2_tex_2(sK5,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (22793)------------------------------
% 0.22/0.51  % (22793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22793)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (22793)Memory used [KB]: 6908
% 0.22/0.51  % (22793)Time elapsed: 0.083 s
% 0.22/0.51  % (22793)------------------------------
% 0.22/0.51  % (22793)------------------------------
% 0.22/0.51  % (22788)Refutation not found, incomplete strategy% (22788)------------------------------
% 0.22/0.51  % (22788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22788)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22788)Memory used [KB]: 1663
% 0.22/0.51  % (22788)Time elapsed: 0.105 s
% 0.22/0.51  % (22788)------------------------------
% 0.22/0.51  % (22788)------------------------------
% 0.22/0.51  % (22780)Success in time 0.15 s
%------------------------------------------------------------------------------
