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
% DateTime   : Thu Dec  3 13:09:25 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  145 (6820 expanded)
%              Number of leaves         :   13 (2186 expanded)
%              Depth                    :   54
%              Number of atoms          :  714 (67472 expanded)
%              Number of equality atoms :   47 (6202 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f491,plain,(
    $false ),
    inference(subsumption_resolution,[],[f490,f40])).

fof(f40,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

% (12429)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

% (12432)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f490,plain,(
    ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f489,f162])).

fof(f162,plain,(
    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X8,X9] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X8,X9)
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X8 ) ),
    inference(subsumption_resolution,[],[f117,f135])).

fof(f135,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(subsumption_resolution,[],[f134,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f134,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f125,f69])).

fof(f69,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f59,f48])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f125,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(superposition,[],[f48,f113])).

fof(f113,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f112,f36])).

fof(f112,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X4] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(X4)
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f86,f48])).

fof(f86,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X3
      | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) ) ),
    inference(superposition,[],[f61,f78])).

fof(f78,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(resolution,[],[f71,f36])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(subsumption_resolution,[],[f70,f69])).

fof(f70,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f49,f68])).

% (12441)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f68,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f58,f48])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f117,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X8,X9)
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X8 ) ),
    inference(backward_demodulation,[],[f89,f113])).

fof(f89,plain,(
    ! [X8,X9] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X8,X9)
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X8
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ) ),
    inference(superposition,[],[f60,f78])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f489,plain,(
    ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f488,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f488,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f487,f162])).

fof(f487,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f486,f146])).

fof(f146,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f141,f114])).

fof(f114,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f78,f113])).

fof(f141,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f135,f59])).

fof(f486,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f485,f38])).

fof(f38,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f485,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f484,f395])).

fof(f395,plain,(
    ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f64,f394])).

fof(f394,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f393,f36])).

fof(f393,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f392,f38])).

fof(f392,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f391,f40])).

fof(f391,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f390,f41])).

fof(f390,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f389])).

fof(f389,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f388,f337])).

fof(f337,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1,sK2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f51,f67])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f42,f45])).

fof(f45,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
                    & v4_pre_topc(sK4(X0,X1,X2),X1)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
        & v4_pre_topc(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f388,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f387,f332])).

fof(f332,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f331,f36])).

fof(f331,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f330,f38])).

fof(f330,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f325,f41])).

fof(f325,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f324,f40])).

fof(f324,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v4_pre_topc(sK4(X0,X1,sK2),X1)
      | v5_pre_topc(sK2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f52,f67])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | v4_pre_topc(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f387,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f386])).

fof(f386,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f385,f365])).

fof(f365,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f364,f36])).

fof(f364,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f363,f38])).

fof(f363,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f358,f41])).

fof(f358,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f357,f40])).

fof(f357,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X0)
      | v5_pre_topc(sK2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f53,f67])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f385,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f384,f41])).

fof(f384,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK1)
      | v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) ),
    inference(resolution,[],[f383,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f383,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK1)
      | v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) ) ),
    inference(resolution,[],[f382,f172])).

fof(f172,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f171,f162])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f169,f36])).

fof(f169,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(sK0)
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f56,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

% (12435)Refutation not found, incomplete strategy% (12435)------------------------------
% (12435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12435)Termination reason: Refutation not found, incomplete strategy

% (12435)Memory used [KB]: 10874
% (12435)Time elapsed: 0.194 s
% (12435)------------------------------
% (12435)------------------------------
fof(f382,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(forward_demodulation,[],[f381,f162])).

fof(f381,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f380,f40])).

fof(f380,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(forward_demodulation,[],[f379,f162])).

fof(f379,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f378,f41])).

fof(f378,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(forward_demodulation,[],[f377,f162])).

fof(f377,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f376,f146])).

fof(f376,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f375,f38])).

fof(f375,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(resolution,[],[f372,f63])).

fof(f63,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f46,f45])).

fof(f46,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f372,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(sK2,X2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK2,X0),X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f50,f67])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(backward_demodulation,[],[f47,f45])).

fof(f47,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f484,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f483,f337])).

fof(f483,plain,(
    ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f482,f38])).

fof(f482,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f481,f395])).

fof(f481,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f480,f40])).

fof(f480,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f479,f41])).

fof(f479,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f478,f333])).

fof(f333,plain,(
    ! [X0] :
      ( v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2),X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f326,f146])).

fof(f326,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2),X0)
      | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(superposition,[],[f324,f162])).

fof(f478,plain,
    ( ~ v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f472,f400])).

fof(f400,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f399,f36])).

fof(f399,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f398,f38])).

fof(f398,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f397,f40])).

fof(f397,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f396,f41])).

fof(f396,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f394,f372])).

fof(f472,plain,(
    ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f471,f38])).

fof(f471,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f470,f395])).

fof(f470,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f467,f41])).

fof(f467,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) ),
    inference(resolution,[],[f444,f40])).

fof(f444,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),sK0) ) ),
    inference(subsumption_resolution,[],[f443,f62])).

fof(f443,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),sK0) ) ),
    inference(subsumption_resolution,[],[f442,f35])).

fof(f442,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f439,f36])).

fof(f439,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f366,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f366,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f359,f146])).

fof(f359,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(superposition,[],[f357,f162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:19:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (12438)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (12430)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (12422)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.57  % (12428)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.57  % (12424)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.57  % (12431)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.57  % (12427)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.69/0.58  % (12439)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.69/0.58  % (12421)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.69/0.58  % (12415)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.69/0.59  % (12418)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.69/0.59  % (12417)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.69/0.59  % (12420)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.69/0.59  % (12417)Refutation not found, incomplete strategy% (12417)------------------------------
% 1.69/0.59  % (12417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (12417)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (12417)Memory used [KB]: 10746
% 1.69/0.59  % (12417)Time elapsed: 0.164 s
% 1.69/0.59  % (12417)------------------------------
% 1.69/0.59  % (12417)------------------------------
% 1.69/0.59  % (12419)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.69/0.59  % (12435)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.69/0.60  % (12426)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.69/0.60  % (12440)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.69/0.60  % (12443)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.69/0.60  % (12442)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.69/0.61  % (12416)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.69/0.61  % (12425)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.69/0.61  % (12422)Refutation found. Thanks to Tanya!
% 1.69/0.61  % SZS status Theorem for theBenchmark
% 1.69/0.61  % (12434)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.69/0.61  % SZS output start Proof for theBenchmark
% 1.69/0.61  fof(f491,plain,(
% 1.69/0.61    $false),
% 1.69/0.61    inference(subsumption_resolution,[],[f490,f40])).
% 1.69/0.61  fof(f40,plain,(
% 1.69/0.61    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.69/0.61    inference(cnf_transformation,[],[f28])).
% 1.69/0.61  fof(f28,plain,(
% 1.69/0.61    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.69/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27,f26,f25,f24])).
% 1.69/0.61  fof(f24,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  % (12429)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.69/0.61  fof(f25,plain,(
% 1.69/0.61    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f26,plain,(
% 1.69/0.61    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f27,plain,(
% 1.69/0.61    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(sK3))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f23,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.69/0.61    inference(flattening,[],[f22])).
% 1.69/0.61  fof(f22,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.69/0.61    inference(nnf_transformation,[],[f11])).
% 1.69/0.61  fof(f11,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.69/0.61    inference(flattening,[],[f10])).
% 1.69/0.61  fof(f10,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.69/0.61    inference(ennf_transformation,[],[f9])).
% 1.69/0.61  fof(f9,negated_conjecture,(
% 1.69/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 1.69/0.61    inference(negated_conjecture,[],[f8])).
% 1.69/0.61  % (12432)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.69/0.61  fof(f8,conjecture,(
% 1.69/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 1.69/0.61  fof(f490,plain,(
% 1.69/0.61    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.69/0.61    inference(forward_demodulation,[],[f489,f162])).
% 1.69/0.61  fof(f162,plain,(
% 1.69/0.61    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.69/0.61    inference(equality_resolution,[],[f136])).
% 1.69/0.61  fof(f136,plain,(
% 1.69/0.61    ( ! [X8,X9] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X8,X9) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X8) )),
% 1.69/0.61    inference(subsumption_resolution,[],[f117,f135])).
% 1.69/0.61  fof(f135,plain,(
% 1.69/0.61    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.69/0.61    inference(subsumption_resolution,[],[f134,f36])).
% 1.69/0.61  fof(f36,plain,(
% 1.69/0.61    l1_pre_topc(sK0)),
% 1.69/0.61    inference(cnf_transformation,[],[f28])).
% 1.69/0.61  fof(f134,plain,(
% 1.69/0.61    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~l1_pre_topc(sK0)),
% 1.69/0.61    inference(resolution,[],[f125,f69])).
% 1.69/0.61  fof(f69,plain,(
% 1.69/0.61    ( ! [X0] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 1.69/0.61    inference(resolution,[],[f59,f48])).
% 1.69/0.61  fof(f48,plain,(
% 1.69/0.61    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f12])).
% 1.69/0.61  fof(f12,plain,(
% 1.69/0.61    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.69/0.61    inference(ennf_transformation,[],[f5])).
% 1.69/0.61  fof(f5,axiom,(
% 1.69/0.61    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.69/0.61  fof(f59,plain,(
% 1.69/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.69/0.61    inference(cnf_transformation,[],[f19])).
% 1.69/0.61  fof(f19,plain,(
% 1.69/0.61    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.69/0.61    inference(ennf_transformation,[],[f4])).
% 1.69/0.61  fof(f4,axiom,(
% 1.69/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 1.69/0.61  fof(f125,plain,(
% 1.69/0.61    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.69/0.61    inference(superposition,[],[f48,f113])).
% 1.69/0.61  fof(f113,plain,(
% 1.69/0.61    u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.69/0.61    inference(subsumption_resolution,[],[f112,f36])).
% 1.69/0.61  fof(f112,plain,(
% 1.69/0.61    u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)),
% 1.69/0.61    inference(equality_resolution,[],[f103])).
% 1.69/0.61  fof(f103,plain,(
% 1.69/0.61    ( ! [X4] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = u1_pre_topc(X4) | ~l1_pre_topc(X4)) )),
% 1.69/0.61    inference(resolution,[],[f86,f48])).
% 1.69/0.61  fof(f86,plain,(
% 1.69/0.61    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X3 | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )),
% 1.69/0.61    inference(superposition,[],[f61,f78])).
% 1.69/0.61  fof(f78,plain,(
% 1.69/0.61    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 1.69/0.61    inference(resolution,[],[f71,f36])).
% 1.69/0.61  fof(f71,plain,(
% 1.69/0.61    ( ! [X0] : (~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )),
% 1.69/0.61    inference(subsumption_resolution,[],[f70,f69])).
% 1.69/0.61  fof(f70,plain,(
% 1.69/0.61    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 1.69/0.61    inference(resolution,[],[f49,f68])).
% 1.69/0.61  % (12441)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.69/0.61  fof(f68,plain,(
% 1.69/0.61    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 1.69/0.61    inference(resolution,[],[f58,f48])).
% 1.69/0.61  fof(f58,plain,(
% 1.69/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.69/0.61    inference(cnf_transformation,[],[f19])).
% 1.69/0.61  fof(f49,plain,(
% 1.69/0.61    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f14])).
% 1.69/0.61  fof(f14,plain,(
% 1.69/0.61    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.69/0.61    inference(flattening,[],[f13])).
% 1.69/0.61  fof(f13,plain,(
% 1.69/0.61    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.69/0.61    inference(ennf_transformation,[],[f2])).
% 1.69/0.61  fof(f2,axiom,(
% 1.69/0.61    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.69/0.61  fof(f61,plain,(
% 1.69/0.61    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.69/0.61    inference(cnf_transformation,[],[f20])).
% 1.69/0.61  fof(f20,plain,(
% 1.69/0.61    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.69/0.61    inference(ennf_transformation,[],[f6])).
% 1.69/0.61  fof(f6,axiom,(
% 1.69/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.69/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.69/0.61  fof(f117,plain,(
% 1.69/0.61    ( ! [X8,X9] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X8,X9) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X8) )),
% 1.69/0.61    inference(backward_demodulation,[],[f89,f113])).
% 1.69/0.61  fof(f89,plain,(
% 1.69/0.61    ( ! [X8,X9] : (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X8,X9) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X8 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) )),
% 1.69/0.61    inference(superposition,[],[f60,f78])).
% 1.69/0.61  fof(f60,plain,(
% 1.69/0.61    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.69/0.61    inference(cnf_transformation,[],[f20])).
% 1.69/0.61  fof(f489,plain,(
% 1.69/0.61    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 1.69/0.61    inference(subsumption_resolution,[],[f488,f41])).
% 1.69/0.62  fof(f41,plain,(
% 1.69/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.69/0.62    inference(cnf_transformation,[],[f28])).
% 1.69/0.62  fof(f488,plain,(
% 1.69/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 1.69/0.62    inference(forward_demodulation,[],[f487,f162])).
% 1.69/0.62  fof(f487,plain,(
% 1.69/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 1.69/0.62    inference(subsumption_resolution,[],[f486,f146])).
% 1.69/0.62  fof(f146,plain,(
% 1.69/0.62    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.69/0.62    inference(forward_demodulation,[],[f141,f114])).
% 1.69/0.62  fof(f114,plain,(
% 1.69/0.62    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0))),
% 1.69/0.62    inference(backward_demodulation,[],[f78,f113])).
% 1.69/0.62  fof(f141,plain,(
% 1.69/0.62    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(sK0)))),
% 1.69/0.62    inference(resolution,[],[f135,f59])).
% 1.69/0.62  fof(f486,plain,(
% 1.69/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.69/0.62    inference(subsumption_resolution,[],[f485,f38])).
% 1.69/0.62  fof(f38,plain,(
% 1.69/0.62    l1_pre_topc(sK1)),
% 1.69/0.62    inference(cnf_transformation,[],[f28])).
% 1.69/0.62  fof(f485,plain,(
% 1.69/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.69/0.62    inference(subsumption_resolution,[],[f484,f395])).
% 1.69/0.62  fof(f395,plain,(
% 1.69/0.62    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 1.69/0.62    inference(subsumption_resolution,[],[f64,f394])).
% 1.69/0.62  fof(f394,plain,(
% 1.69/0.62    v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.62    inference(subsumption_resolution,[],[f393,f36])).
% 1.69/0.62  fof(f393,plain,(
% 1.69/0.62    v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.62    inference(subsumption_resolution,[],[f392,f38])).
% 1.69/0.62  fof(f392,plain,(
% 1.69/0.62    v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.62    inference(subsumption_resolution,[],[f391,f40])).
% 1.69/0.62  fof(f391,plain,(
% 1.69/0.62    v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.62    inference(subsumption_resolution,[],[f390,f41])).
% 1.69/0.62  fof(f390,plain,(
% 1.69/0.62    v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.62    inference(duplicate_literal_removal,[],[f389])).
% 1.69/0.62  fof(f389,plain,(
% 1.69/0.62    v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.62    inference(resolution,[],[f388,f337])).
% 1.69/0.62  fof(f337,plain,(
% 1.69/0.62    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1,sK2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.69/0.62    inference(resolution,[],[f51,f67])).
% 1.69/0.62  fof(f67,plain,(
% 1.69/0.62    v1_funct_1(sK2)),
% 1.69/0.62    inference(forward_demodulation,[],[f42,f45])).
% 1.69/0.62  fof(f45,plain,(
% 1.69/0.62    sK2 = sK3),
% 1.69/0.62    inference(cnf_transformation,[],[f28])).
% 1.69/0.62  fof(f42,plain,(
% 1.69/0.62    v1_funct_1(sK3)),
% 1.69/0.62    inference(cnf_transformation,[],[f28])).
% 1.69/0.62  fof(f51,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.69/0.62    inference(cnf_transformation,[],[f32])).
% 1.69/0.62  fof(f32,plain,(
% 1.69/0.62    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) & v4_pre_topc(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.69/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.69/0.62  fof(f31,plain,(
% 1.69/0.62    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) & v4_pre_topc(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.69/0.62    introduced(choice_axiom,[])).
% 1.69/0.62  fof(f30,plain,(
% 1.69/0.62    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.69/0.62    inference(rectify,[],[f29])).
% 1.69/0.62  fof(f29,plain,(
% 1.69/0.62    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.69/0.62    inference(nnf_transformation,[],[f16])).
% 1.69/0.62  fof(f16,plain,(
% 1.69/0.62    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.69/0.62    inference(flattening,[],[f15])).
% 1.69/0.62  fof(f15,plain,(
% 1.69/0.62    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.69/0.62    inference(ennf_transformation,[],[f3])).
% 1.69/0.62  fof(f3,axiom,(
% 1.69/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 1.69/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).
% 1.69/0.62  fof(f388,plain,(
% 1.69/0.62    ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.62    inference(subsumption_resolution,[],[f387,f332])).
% 1.69/0.62  fof(f332,plain,(
% 1.69/0.62    v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.62    inference(subsumption_resolution,[],[f331,f36])).
% 1.69/0.62  fof(f331,plain,(
% 1.69/0.62    v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.62    inference(subsumption_resolution,[],[f330,f38])).
% 1.69/0.62  fof(f330,plain,(
% 1.69/0.62    v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.62    inference(subsumption_resolution,[],[f325,f41])).
% 1.69/0.62  fof(f325,plain,(
% 1.69/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.62    inference(resolution,[],[f324,f40])).
% 1.69/0.62  fof(f324,plain,(
% 1.69/0.62    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v4_pre_topc(sK4(X0,X1,sK2),X1) | v5_pre_topc(sK2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.69/0.62    inference(resolution,[],[f52,f67])).
% 1.69/0.62  fof(f52,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | v4_pre_topc(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.69/0.62    inference(cnf_transformation,[],[f32])).
% 1.69/0.62  fof(f387,plain,(
% 1.69/0.62    v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(sK4(sK0,sK1,sK2),sK1)),
% 1.69/0.62    inference(duplicate_literal_removal,[],[f386])).
% 1.69/0.62  fof(f386,plain,(
% 1.69/0.62    v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.62    inference(resolution,[],[f385,f365])).
% 1.69/0.62  fof(f365,plain,(
% 1.69/0.62    ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) | v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.62    inference(subsumption_resolution,[],[f364,f36])).
% 1.69/0.62  fof(f364,plain,(
% 1.69/0.62    ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.62    inference(subsumption_resolution,[],[f363,f38])).
% 1.69/0.62  fof(f363,plain,(
% 1.69/0.62    ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.62    inference(subsumption_resolution,[],[f358,f41])).
% 1.69/0.62  fof(f358,plain,(
% 1.69/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.62    inference(resolution,[],[f357,f40])).
% 1.69/0.62  fof(f357,plain,(
% 1.69/0.62    ( ! [X0,X1] : (~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X0) | v5_pre_topc(sK2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.69/0.62    inference(resolution,[],[f53,f67])).
% 1.69/0.62  fof(f53,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.69/0.62    inference(cnf_transformation,[],[f32])).
% 1.69/0.62  fof(f385,plain,(
% 1.69/0.62    ( ! [X0] : (v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f384,f41])).
% 1.69/0.62  fof(f384,plain,(
% 1.69/0.62    ( ! [X0] : (~v4_pre_topc(X0,sK1) | v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))) )),
% 1.69/0.62    inference(resolution,[],[f383,f62])).
% 1.69/0.62  fof(f62,plain,(
% 1.69/0.62    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.62    inference(cnf_transformation,[],[f21])).
% 1.69/0.62  fof(f21,plain,(
% 1.69/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.62    inference(ennf_transformation,[],[f1])).
% 1.69/0.62  fof(f1,axiom,(
% 1.69/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.69/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 1.69/0.62  fof(f383,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK1) | v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)) )),
% 1.69/0.62    inference(resolution,[],[f382,f172])).
% 1.69/0.62  fof(f172,plain,(
% 1.69/0.62    ( ! [X0] : (~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 1.69/0.62    inference(forward_demodulation,[],[f171,f162])).
% 1.69/0.62  fof(f171,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v4_pre_topc(X0,sK0)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f169,f36])).
% 1.69/0.62  fof(f169,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(X0,sK0)) )),
% 1.69/0.62    inference(resolution,[],[f56,f35])).
% 1.69/0.62  fof(f35,plain,(
% 1.69/0.62    v2_pre_topc(sK0)),
% 1.69/0.62    inference(cnf_transformation,[],[f28])).
% 1.69/0.62  fof(f56,plain,(
% 1.69/0.62    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 1.69/0.62    inference(cnf_transformation,[],[f34])).
% 1.69/0.62  fof(f34,plain,(
% 1.69/0.62    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.69/0.62    inference(flattening,[],[f33])).
% 1.69/0.62  fof(f33,plain,(
% 1.69/0.62    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.69/0.62    inference(nnf_transformation,[],[f18])).
% 1.69/0.62  fof(f18,plain,(
% 1.69/0.62    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.69/0.62    inference(flattening,[],[f17])).
% 1.69/0.62  fof(f17,plain,(
% 1.69/0.62    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.69/0.62    inference(ennf_transformation,[],[f7])).
% 1.69/0.62  fof(f7,axiom,(
% 1.69/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.69/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).
% 1.69/0.62  % (12435)Refutation not found, incomplete strategy% (12435)------------------------------
% 1.69/0.62  % (12435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.62  % (12435)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.62  
% 1.69/0.62  % (12435)Memory used [KB]: 10874
% 1.69/0.62  % (12435)Time elapsed: 0.194 s
% 1.69/0.62  % (12435)------------------------------
% 1.69/0.62  % (12435)------------------------------
% 1.69/0.62  fof(f382,plain,(
% 1.69/0.62    ( ! [X0] : (v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v5_pre_topc(sK2,sK0,sK1)) )),
% 1.69/0.62    inference(forward_demodulation,[],[f381,f162])).
% 1.69/0.62  fof(f381,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,sK0,sK1)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f380,f40])).
% 1.69/0.62  fof(f380,plain,(
% 1.69/0.62    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,sK0,sK1)) )),
% 1.69/0.62    inference(forward_demodulation,[],[f379,f162])).
% 1.69/0.62  fof(f379,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,sK0,sK1)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f378,f41])).
% 1.69/0.62  fof(f378,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,sK0,sK1)) )),
% 1.69/0.62    inference(forward_demodulation,[],[f377,f162])).
% 1.69/0.62  fof(f377,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,sK0,sK1)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f376,f146])).
% 1.69/0.62  fof(f376,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,sK0,sK1)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f375,f38])).
% 1.69/0.62  fof(f375,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,sK0,sK1)) )),
% 1.69/0.62    inference(resolution,[],[f372,f63])).
% 1.69/0.62  fof(f63,plain,(
% 1.69/0.62    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.62    inference(backward_demodulation,[],[f46,f45])).
% 1.69/0.62  fof(f46,plain,(
% 1.69/0.62    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.62    inference(cnf_transformation,[],[f28])).
% 1.69/0.62  fof(f372,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (~v5_pre_topc(sK2,X2,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1)) | v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK2,X0),X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2)) )),
% 1.69/0.62    inference(resolution,[],[f50,f67])).
% 1.69/0.62  fof(f50,plain,(
% 1.69/0.62    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.69/0.62    inference(cnf_transformation,[],[f32])).
% 1.69/0.62  fof(f64,plain,(
% 1.69/0.62    ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 1.69/0.62    inference(backward_demodulation,[],[f47,f45])).
% 1.69/0.62  fof(f47,plain,(
% 1.69/0.62    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.62    inference(cnf_transformation,[],[f28])).
% 1.69/0.62  fof(f484,plain,(
% 1.69/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.69/0.62    inference(resolution,[],[f483,f337])).
% 1.69/0.62  fof(f483,plain,(
% 1.69/0.62    ~m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.69/0.62    inference(subsumption_resolution,[],[f482,f38])).
% 1.69/0.62  fof(f482,plain,(
% 1.69/0.62    ~m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.69/0.62    inference(subsumption_resolution,[],[f481,f395])).
% 1.69/0.62  fof(f481,plain,(
% 1.69/0.62    ~m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK1)),
% 1.69/0.62    inference(subsumption_resolution,[],[f480,f40])).
% 1.69/0.62  fof(f480,plain,(
% 1.69/0.62    ~m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK1)),
% 1.69/0.62    inference(subsumption_resolution,[],[f479,f41])).
% 1.69/0.62  fof(f479,plain,(
% 1.69/0.62    ~m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK1)),
% 1.69/0.62    inference(resolution,[],[f478,f333])).
% 1.69/0.62  fof(f333,plain,(
% 1.69/0.62    ( ! [X0] : (v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f326,f146])).
% 1.69/0.62  fof(f326,plain,(
% 1.69/0.62    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2),X0) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )),
% 1.69/0.62    inference(superposition,[],[f324,f162])).
% 1.69/0.62  fof(f478,plain,(
% 1.69/0.62    ~v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1) | ~m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.69/0.62    inference(resolution,[],[f472,f400])).
% 1.69/0.62  fof(f400,plain,(
% 1.69/0.62    ( ! [X0] : (v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f399,f36])).
% 1.69/0.62  fof(f399,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f398,f38])).
% 1.69/0.62  fof(f398,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f397,f40])).
% 1.69/0.62  fof(f397,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f396,f41])).
% 1.69/0.62  fof(f396,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) )),
% 1.69/0.62    inference(resolution,[],[f394,f372])).
% 1.69/0.62  fof(f472,plain,(
% 1.69/0.62    ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)),
% 1.69/0.62    inference(subsumption_resolution,[],[f471,f38])).
% 1.69/0.62  fof(f471,plain,(
% 1.69/0.62    ~l1_pre_topc(sK1) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)),
% 1.69/0.62    inference(subsumption_resolution,[],[f470,f395])).
% 1.69/0.62  fof(f470,plain,(
% 1.69/0.62    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK1) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)),
% 1.69/0.62    inference(subsumption_resolution,[],[f467,f41])).
% 1.69/0.62  fof(f467,plain,(
% 1.69/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK1) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)),
% 1.69/0.62    inference(resolution,[],[f444,f40])).
% 1.69/0.62  fof(f444,plain,(
% 1.69/0.62    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),sK0)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f443,f62])).
% 1.69/0.62  fof(f443,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),sK0)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f442,f35])).
% 1.69/0.62  fof(f442,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),sK0) | ~v2_pre_topc(sK0)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f439,f36])).
% 1.69/0.62  fof(f439,plain,(
% 1.69/0.62    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 1.69/0.62    inference(resolution,[],[f366,f54])).
% 1.69/0.62  fof(f54,plain,(
% 1.69/0.62    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.69/0.62    inference(cnf_transformation,[],[f34])).
% 1.69/0.62  fof(f366,plain,(
% 1.69/0.62    ( ! [X0] : (~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0)) )),
% 1.69/0.62    inference(subsumption_resolution,[],[f359,f146])).
% 1.69/0.62  fof(f359,plain,(
% 1.69/0.62    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )),
% 1.69/0.62    inference(superposition,[],[f357,f162])).
% 1.69/0.62  % SZS output end Proof for theBenchmark
% 1.69/0.62  % (12422)------------------------------
% 1.69/0.62  % (12422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.62  % (12422)Termination reason: Refutation
% 1.69/0.62  
% 1.69/0.62  % (12422)Memory used [KB]: 6780
% 1.69/0.62  % (12422)Time elapsed: 0.127 s
% 1.69/0.62  % (12422)------------------------------
% 1.69/0.62  % (12422)------------------------------
% 1.69/0.62  % (12436)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.69/0.62  % (12414)Success in time 0.261 s
%------------------------------------------------------------------------------
