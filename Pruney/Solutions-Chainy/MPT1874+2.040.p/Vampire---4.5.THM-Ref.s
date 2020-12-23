%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 238 expanded)
%              Number of leaves         :   19 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  380 (1301 expanded)
%              Number of equality atoms :   33 ( 163 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f298,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f264,f273,f280,f282,f288])).

fof(f288,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f132,f70])).

fof(f70,plain,
    ( spl7_1
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f132,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f129,f89])).

fof(f89,plain,(
    r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
          & r2_hidden(X2,sK3)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
        & r2_hidden(X2,sK3)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
      & r2_hidden(sK4,sK3)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f129,plain,(
    ! [X5] :
      ( ~ r1_tarski(sK3,X5)
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f107,f46])).

fof(f46,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f107,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ v1_xboole_0(X1)
      | ~ r1_tarski(X3,X1) ) ),
    inference(resolution,[],[f66,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f282,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f133,f83])).

fof(f83,plain,
    ( spl7_4
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f133,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f129,f104])).

fof(f104,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f63,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f280,plain,
    ( spl7_1
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl7_1
    | spl7_11 ),
    inference(subsumption_resolution,[],[f278,f72])).

fof(f72,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f278,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | spl7_11 ),
    inference(subsumption_resolution,[],[f274,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f274,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | spl7_11 ),
    inference(resolution,[],[f259,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f60,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f259,plain,
    ( ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl7_11
  <=> m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f273,plain,
    ( spl7_4
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f271,f84])).

fof(f84,plain,
    ( ~ v1_xboole_0(sK3)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f271,plain,
    ( v1_xboole_0(sK3)
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f269,f46])).

fof(f269,plain,
    ( ~ r2_hidden(sK4,sK3)
    | v1_xboole_0(sK3)
    | spl7_4
    | spl7_12 ),
    inference(resolution,[],[f268,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f268,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f265,f84])).

fof(f265,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK4,sK3)
    | spl7_12 ),
    inference(resolution,[],[f263,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X1),X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X1),X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f155,f59])).

% (22317)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f155,plain,(
    ! [X4,X3] :
      ( r1_tarski(k6_domain_1(X4,X3),X4)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f60,f64])).

fof(f263,plain,
    ( ~ r1_tarski(k1_tarski(sK4),sK3)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl7_12
  <=> r1_tarski(k1_tarski(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f264,plain,
    ( ~ spl7_11
    | ~ spl7_12
    | spl7_1 ),
    inference(avatar_split_clause,[],[f255,f70,f261,f257])).

fof(f255,plain,
    ( ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f243,f188])).

fof(f188,plain,(
    sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f187,f44])).

fof(f44,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f187,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | sP0(sK2,sK3) ),
    inference(resolution,[],[f185,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f185,plain,(
    sP1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f184,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f184,plain,
    ( sP1(sK3,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f183,f41])).

fof(f41,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f183,plain,
    ( sP1(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f180,f42])).

fof(f42,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f180,plain,
    ( sP1(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f54,f43])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f13,f22,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f243,plain,
    ( ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK2,sK3)
    | spl7_1 ),
    inference(trivial_inequality_removal,[],[f241])).

fof(f241,plain,
    ( k1_tarski(sK4) != k1_tarski(sK4)
    | ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK2,sK3)
    | spl7_1 ),
    inference(superposition,[],[f141,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1)))
          & r1_tarski(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1)))
        & r1_tarski(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

% (22334)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f141,plain,
    ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4)))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f140,f72])).

fof(f140,plain,
    ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f139,f45])).

fof(f139,plain,
    ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(superposition,[],[f47,f59])).

fof(f47,plain,(
    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (22336)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (22340)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (22328)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (22331)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (22323)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (22315)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.58  % (22340)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % (22318)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (22324)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (22323)Refutation not found, incomplete strategy% (22323)------------------------------
% 0.21/0.58  % (22323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (22323)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (22323)Memory used [KB]: 10746
% 0.21/0.58  % (22323)Time elapsed: 0.092 s
% 0.21/0.58  % (22323)------------------------------
% 0.21/0.58  % (22323)------------------------------
% 0.21/0.59  % (22316)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.59  % (22313)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.59  % (22314)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.59  % (22319)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.59  % (22330)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.60  % (22321)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.60  % (22315)Refutation not found, incomplete strategy% (22315)------------------------------
% 0.21/0.60  % (22315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (22315)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (22315)Memory used [KB]: 10874
% 0.21/0.60  % (22315)Time elapsed: 0.179 s
% 0.21/0.60  % (22315)------------------------------
% 0.21/0.60  % (22315)------------------------------
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f298,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(avatar_sat_refutation,[],[f264,f273,f280,f282,f288])).
% 0.21/0.60  fof(f288,plain,(
% 0.21/0.60    ~spl7_1),
% 0.21/0.60    inference(avatar_split_clause,[],[f132,f70])).
% 0.21/0.60  fof(f70,plain,(
% 0.21/0.60    spl7_1 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.60  fof(f132,plain,(
% 0.21/0.60    ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.60    inference(resolution,[],[f129,f89])).
% 0.21/0.60  fof(f89,plain,(
% 0.21/0.60    r1_tarski(sK3,u1_struct_0(sK2))),
% 0.21/0.60    inference(resolution,[],[f64,f43])).
% 0.21/0.60  fof(f43,plain,(
% 0.21/0.60    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.60    inference(cnf_transformation,[],[f27])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ((k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f26,f25,f24])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f25,plain,(
% 0.21/0.60    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) => (k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f11,plain,(
% 0.21/0.60    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f10])).
% 0.21/0.60  fof(f10,plain,(
% 0.21/0.60    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,negated_conjecture,(
% 0.21/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.21/0.60    inference(negated_conjecture,[],[f8])).
% 0.21/0.60  fof(f8,conjecture,(
% 0.21/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).
% 0.21/0.60  fof(f64,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f39])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.60    inference(nnf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.60  fof(f129,plain,(
% 0.21/0.60    ( ! [X5] : (~r1_tarski(sK3,X5) | ~v1_xboole_0(X5)) )),
% 0.21/0.60    inference(resolution,[],[f107,f46])).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    r2_hidden(sK4,sK3)),
% 0.21/0.60    inference(cnf_transformation,[],[f27])).
% 0.21/0.60  fof(f107,plain,(
% 0.21/0.60    ( ! [X2,X3,X1] : (~r2_hidden(X2,X3) | ~v1_xboole_0(X1) | ~r1_tarski(X3,X1)) )),
% 0.21/0.60    inference(resolution,[],[f66,f65])).
% 0.21/0.60  fof(f65,plain,(
% 0.21/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f39])).
% 0.21/0.60  fof(f66,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.60  fof(f282,plain,(
% 0.21/0.60    ~spl7_4),
% 0.21/0.60    inference(avatar_split_clause,[],[f133,f83])).
% 0.21/0.60  fof(f83,plain,(
% 0.21/0.60    spl7_4 <=> v1_xboole_0(sK3)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.60  fof(f133,plain,(
% 0.21/0.60    ~v1_xboole_0(sK3)),
% 0.21/0.60    inference(resolution,[],[f129,f104])).
% 0.21/0.60  fof(f104,plain,(
% 0.21/0.60    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f103])).
% 0.21/0.60  fof(f103,plain,(
% 0.21/0.60    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.60    inference(resolution,[],[f63,f62])).
% 0.21/0.60  fof(f62,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f38])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.60    inference(rectify,[],[f35])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.60    inference(nnf_transformation,[],[f19])).
% 0.21/0.60  fof(f19,plain,(
% 0.21/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.60  fof(f63,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f38])).
% 0.21/0.60  fof(f280,plain,(
% 0.21/0.60    spl7_1 | spl7_11),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f279])).
% 0.21/0.60  fof(f279,plain,(
% 0.21/0.60    $false | (spl7_1 | spl7_11)),
% 0.21/0.60    inference(subsumption_resolution,[],[f278,f72])).
% 0.21/0.60  fof(f72,plain,(
% 0.21/0.60    ~v1_xboole_0(u1_struct_0(sK2)) | spl7_1),
% 0.21/0.60    inference(avatar_component_clause,[],[f70])).
% 0.21/0.60  fof(f278,plain,(
% 0.21/0.60    v1_xboole_0(u1_struct_0(sK2)) | spl7_11),
% 0.21/0.60    inference(subsumption_resolution,[],[f274,f45])).
% 0.21/0.60  fof(f45,plain,(
% 0.21/0.60    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.21/0.60    inference(cnf_transformation,[],[f27])).
% 0.21/0.60  fof(f274,plain,(
% 0.21/0.60    ~m1_subset_1(sK4,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | spl7_11),
% 0.21/0.60    inference(resolution,[],[f259,f159])).
% 0.21/0.60  fof(f159,plain,(
% 0.21/0.60    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f158])).
% 0.21/0.60  fof(f158,plain,(
% 0.21/0.60    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.60    inference(superposition,[],[f60,f59])).
% 0.21/0.60  fof(f59,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.60    inference(flattening,[],[f15])).
% 0.21/0.60  fof(f15,plain,(
% 0.21/0.60    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.60  fof(f60,plain,(
% 0.21/0.60    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f18])).
% 0.21/0.60  fof(f18,plain,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.60    inference(flattening,[],[f17])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.60  fof(f259,plain,(
% 0.21/0.60    ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_11),
% 0.21/0.60    inference(avatar_component_clause,[],[f257])).
% 0.21/0.60  fof(f257,plain,(
% 0.21/0.60    spl7_11 <=> m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.60  fof(f273,plain,(
% 0.21/0.60    spl7_4 | spl7_12),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f272])).
% 0.21/0.60  fof(f272,plain,(
% 0.21/0.60    $false | (spl7_4 | spl7_12)),
% 0.21/0.60    inference(subsumption_resolution,[],[f271,f84])).
% 0.21/0.60  fof(f84,plain,(
% 0.21/0.60    ~v1_xboole_0(sK3) | spl7_4),
% 0.21/0.60    inference(avatar_component_clause,[],[f83])).
% 0.21/0.60  fof(f271,plain,(
% 0.21/0.60    v1_xboole_0(sK3) | (spl7_4 | spl7_12)),
% 0.21/0.60    inference(subsumption_resolution,[],[f269,f46])).
% 0.21/0.60  fof(f269,plain,(
% 0.21/0.60    ~r2_hidden(sK4,sK3) | v1_xboole_0(sK3) | (spl7_4 | spl7_12)),
% 0.21/0.60    inference(resolution,[],[f268,f56])).
% 0.21/0.60  fof(f56,plain,(
% 0.21/0.60    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f34])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.60    inference(nnf_transformation,[],[f14])).
% 0.21/0.60  fof(f14,plain,(
% 0.21/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.60  fof(f268,plain,(
% 0.21/0.60    ~m1_subset_1(sK4,sK3) | (spl7_4 | spl7_12)),
% 0.21/0.60    inference(subsumption_resolution,[],[f265,f84])).
% 0.21/0.60  fof(f265,plain,(
% 0.21/0.60    v1_xboole_0(sK3) | ~m1_subset_1(sK4,sK3) | spl7_12),
% 0.21/0.60    inference(resolution,[],[f263,f166])).
% 0.21/0.60  fof(f166,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X1),X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f165])).
% 0.21/0.60  fof(f165,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X1),X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.60    inference(superposition,[],[f155,f59])).
% 0.21/0.60  % (22317)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.60  fof(f155,plain,(
% 0.21/0.60    ( ! [X4,X3] : (r1_tarski(k6_domain_1(X4,X3),X4) | v1_xboole_0(X4) | ~m1_subset_1(X3,X4)) )),
% 0.21/0.60    inference(resolution,[],[f60,f64])).
% 0.21/0.60  fof(f263,plain,(
% 0.21/0.60    ~r1_tarski(k1_tarski(sK4),sK3) | spl7_12),
% 0.21/0.60    inference(avatar_component_clause,[],[f261])).
% 0.21/0.60  fof(f261,plain,(
% 0.21/0.60    spl7_12 <=> r1_tarski(k1_tarski(sK4),sK3)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.60  fof(f264,plain,(
% 0.21/0.60    ~spl7_11 | ~spl7_12 | spl7_1),
% 0.21/0.60    inference(avatar_split_clause,[],[f255,f70,f261,f257])).
% 0.21/0.60  fof(f255,plain,(
% 0.21/0.60    ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_1),
% 0.21/0.60    inference(subsumption_resolution,[],[f243,f188])).
% 0.21/0.60  fof(f188,plain,(
% 0.21/0.60    sP0(sK2,sK3)),
% 0.21/0.60    inference(subsumption_resolution,[],[f187,f44])).
% 0.21/0.60  fof(f44,plain,(
% 0.21/0.60    v2_tex_2(sK3,sK2)),
% 0.21/0.60    inference(cnf_transformation,[],[f27])).
% 0.21/0.60  fof(f187,plain,(
% 0.21/0.60    ~v2_tex_2(sK3,sK2) | sP0(sK2,sK3)),
% 0.21/0.60    inference(resolution,[],[f185,f48])).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_tex_2(X0,X1) | sP0(X1,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f29])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP1(X0,X1))),
% 0.21/0.60    inference(rectify,[],[f28])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP1(X1,X0))),
% 0.21/0.60    inference(nnf_transformation,[],[f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.21/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.60  fof(f185,plain,(
% 0.21/0.60    sP1(sK3,sK2)),
% 0.21/0.60    inference(subsumption_resolution,[],[f184,f40])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ~v2_struct_0(sK2)),
% 0.21/0.60    inference(cnf_transformation,[],[f27])).
% 0.21/0.60  fof(f184,plain,(
% 0.21/0.60    sP1(sK3,sK2) | v2_struct_0(sK2)),
% 0.21/0.60    inference(subsumption_resolution,[],[f183,f41])).
% 0.21/0.60  fof(f41,plain,(
% 0.21/0.60    v2_pre_topc(sK2)),
% 0.21/0.60    inference(cnf_transformation,[],[f27])).
% 0.21/0.60  fof(f183,plain,(
% 0.21/0.60    sP1(sK3,sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.60    inference(subsumption_resolution,[],[f180,f42])).
% 0.21/0.60  fof(f42,plain,(
% 0.21/0.60    l1_pre_topc(sK2)),
% 0.21/0.60    inference(cnf_transformation,[],[f27])).
% 0.21/0.60  fof(f180,plain,(
% 0.21/0.60    sP1(sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.60    inference(resolution,[],[f54,f43])).
% 0.21/0.60  fof(f54,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(definition_folding,[],[f13,f22,f21])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.60  fof(f13,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f12])).
% 0.21/0.60  fof(f12,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f7])).
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.21/0.60  fof(f243,plain,(
% 0.21/0.60    ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK2,sK3) | spl7_1),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f241])).
% 0.21/0.60  fof(f241,plain,(
% 0.21/0.60    k1_tarski(sK4) != k1_tarski(sK4) | ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK2,sK3) | spl7_1),
% 0.21/0.60    inference(superposition,[],[f141,f50])).
% 0.21/0.60  fof(f50,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1))) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1))) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f31,plain,(
% 0.21/0.60    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.60    inference(rectify,[],[f30])).
% 0.21/0.60  % (22334)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.61  fof(f30,plain,(
% 0.21/0.61    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.61    inference(nnf_transformation,[],[f21])).
% 0.21/0.61  fof(f141,plain,(
% 0.21/0.61    k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) | spl7_1),
% 0.21/0.61    inference(subsumption_resolution,[],[f140,f72])).
% 0.21/0.61  fof(f140,plain,(
% 0.21/0.61    k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) | v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.61    inference(subsumption_resolution,[],[f139,f45])).
% 0.21/0.61  fof(f139,plain,(
% 0.21/0.61    k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.61    inference(superposition,[],[f47,f59])).
% 0.21/0.61  fof(f47,plain,(
% 0.21/0.61    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))),
% 0.21/0.61    inference(cnf_transformation,[],[f27])).
% 0.21/0.61  % SZS output end Proof for theBenchmark
% 0.21/0.61  % (22340)------------------------------
% 0.21/0.61  % (22340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (22340)Termination reason: Refutation
% 0.21/0.61  
% 0.21/0.61  % (22340)Memory used [KB]: 6396
% 0.21/0.61  % (22340)Time elapsed: 0.163 s
% 0.21/0.61  % (22340)------------------------------
% 0.21/0.61  % (22340)------------------------------
% 0.21/0.61  % (22312)Success in time 0.251 s
%------------------------------------------------------------------------------
