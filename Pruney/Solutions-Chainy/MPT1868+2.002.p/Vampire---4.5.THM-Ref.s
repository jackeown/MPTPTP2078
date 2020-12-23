%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:19 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 511 expanded)
%              Number of leaves         :   33 ( 163 expanded)
%              Depth                    :   15
%              Number of atoms          :  683 (2009 expanded)
%              Number of equality atoms :   73 ( 186 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1823,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f135,f568,f592,f629,f660,f671,f696,f711,f945,f1820])).

fof(f1820,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_37 ),
    inference(avatar_contradiction_clause,[],[f1819])).

fof(f1819,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f1818,f126])).

fof(f126,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_1
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1818,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | spl6_2
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f1817,f160])).

fof(f160,plain,
    ( ~ v2_tex_2(k2_tarski(sK1,sK1),sK0)
    | spl6_2 ),
    inference(backward_demodulation,[],[f68,f158])).

fof(f158,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f153,f129])).

fof(f129,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f153,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f102,f67])).

fof(f67,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f95,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f68,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f1817,plain,
    ( v2_tex_2(k2_tarski(sK1,sK1),sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f1816,f66])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f1816,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(k2_tarski(sK1,sK1),sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f1815,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f1815,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k2_tarski(sK1,sK1),sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_37 ),
    inference(duplicate_literal_removal,[],[f1810])).

fof(f1810,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k2_tarski(sK1,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_37 ),
    inference(resolution,[],[f591,f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK4(X0,k2_tarski(X1,X1)),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f214,f100])).

fof(f100,plain,(
    ! [X0] : ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f69,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f214,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK4(X0,k2_tarski(X1,X1)),X0)
      | v1_xboole_0(k2_tarski(X1,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f87,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f93,f70])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK4(X0,X1),X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK4(X0,X1)) = X1
            & m1_pre_topc(sK4(X0,X1),X0)
            & v1_pre_topc(sK4(X0,X1))
            & ~ v2_struct_0(sK4(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK4(X0,X1)) = X1
        & m1_pre_topc(sK4(X0,X1),X0)
        & v1_pre_topc(sK4(X0,X1))
        & ~ v2_struct_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f591,plain,
    ( ! [X7] :
        ( ~ m1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)),X7)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X7)
        | v2_tex_2(k2_tarski(sK1,sK1),X7) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl6_37
  <=> ! [X7] :
        ( v2_tex_2(k2_tarski(sK1,sK1),X7)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)),X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f945,plain,(
    ~ spl6_31 ),
    inference(avatar_contradiction_clause,[],[f944])).

fof(f944,plain,
    ( $false
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f943,f116])).

fof(f116,plain,(
    ! [X0] : m1_subset_1(X0,k2_tarski(X0,X0)) ),
    inference(resolution,[],[f92,f110])).

fof(f110,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f97,f70])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f61,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f943,plain,
    ( ~ m1_subset_1(sK1,k2_tarski(sK1,sK1))
    | ~ spl6_31 ),
    inference(trivial_inequality_removal,[],[f942])).

fof(f942,plain,
    ( k2_tarski(sK1,sK1) != k2_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k2_tarski(sK1,sK1))
    | ~ spl6_31 ),
    inference(superposition,[],[f567,f157])).

fof(f157,plain,(
    ! [X0] : k2_tarski(X0,X0) = k6_domain_1(k2_tarski(X0,X0),X0) ),
    inference(subsumption_resolution,[],[f150,f100])).

fof(f150,plain,(
    ! [X0] :
      ( k2_tarski(X0,X0) = k6_domain_1(k2_tarski(X0,X0),X0)
      | v1_xboole_0(k2_tarski(X0,X0)) ) ),
    inference(resolution,[],[f102,f116])).

fof(f567,plain,
    ( ! [X2] :
        ( k2_tarski(sK1,sK1) != k6_domain_1(k2_tarski(sK1,sK1),X2)
        | ~ m1_subset_1(X2,k2_tarski(sK1,sK1)) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl6_31
  <=> ! [X2] :
        ( k2_tarski(sK1,sK1) != k6_domain_1(k2_tarski(sK1,sK1),X2)
        | ~ m1_subset_1(X2,k2_tarski(sK1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f711,plain,
    ( ~ spl6_1
    | spl6_47 ),
    inference(avatar_contradiction_clause,[],[f710])).

fof(f710,plain,
    ( $false
    | ~ spl6_1
    | spl6_47 ),
    inference(subsumption_resolution,[],[f709,f65])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f709,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_47 ),
    inference(subsumption_resolution,[],[f708,f66])).

fof(f708,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | spl6_47 ),
    inference(subsumption_resolution,[],[f707,f126])).

fof(f707,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_47 ),
    inference(subsumption_resolution,[],[f704,f64])).

fof(f704,plain,
    ( v2_struct_0(sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_47 ),
    inference(resolution,[],[f692,f232])).

fof(f232,plain,(
    ! [X4,X5] :
      ( v2_pre_topc(sK4(X4,k2_tarski(X5,X5)))
      | v2_struct_0(X4)
      | ~ r2_hidden(X5,u1_struct_0(X4))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4) ) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ r2_hidden(X5,u1_struct_0(X4))
      | v2_pre_topc(sK4(X4,k2_tarski(X5,X5)))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4) ) ),
    inference(resolution,[],[f218,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
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
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f692,plain,
    ( ~ v2_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)))
    | spl6_47 ),
    inference(avatar_component_clause,[],[f690])).

fof(f690,plain,
    ( spl6_47
  <=> v2_pre_topc(sK4(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f696,plain,
    ( spl6_36
    | ~ spl6_47
    | ~ spl6_25
    | spl6_27
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f695,f557,f549,f541,f690,f586])).

fof(f586,plain,
    ( spl6_36
  <=> v1_tdlat_3(sK4(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f541,plain,
    ( spl6_25
  <=> l1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f549,plain,
    ( spl6_27
  <=> v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f557,plain,
    ( spl6_29
  <=> v7_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f695,plain,
    ( ~ v2_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)))
    | v1_tdlat_3(sK4(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_25
    | spl6_27
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f694,f542])).

fof(f542,plain,
    ( l1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f541])).

fof(f694,plain,
    ( ~ v2_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)))
    | v1_tdlat_3(sK4(sK0,k2_tarski(sK1,sK1)))
    | ~ l1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)))
    | spl6_27
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f676,f550])).

fof(f550,plain,
    ( ~ v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f549])).

fof(f676,plain,
    ( ~ v2_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)))
    | v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))
    | v1_tdlat_3(sK4(sK0,k2_tarski(sK1,sK1)))
    | ~ l1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_29 ),
    inference(resolution,[],[f558,f188])).

fof(f188,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f83,f75])).

fof(f75,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | v1_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v2_tdlat_3(X1)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).

fof(f558,plain,
    ( v7_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f557])).

fof(f671,plain,
    ( ~ spl6_1
    | spl6_28 ),
    inference(avatar_contradiction_clause,[],[f670])).

fof(f670,plain,
    ( $false
    | ~ spl6_1
    | spl6_28 ),
    inference(subsumption_resolution,[],[f669,f64])).

fof(f669,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_1
    | spl6_28 ),
    inference(subsumption_resolution,[],[f668,f66])).

fof(f668,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | spl6_28 ),
    inference(subsumption_resolution,[],[f665,f126])).

fof(f665,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_28 ),
    inference(resolution,[],[f555,f237])).

fof(f237,plain,(
    ! [X0,X1] :
      ( l1_struct_0(sK4(X0,k2_tarski(X1,X1)))
      | ~ r2_hidden(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f231,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f231,plain,(
    ! [X6,X7] :
      ( l1_pre_topc(sK4(X6,k2_tarski(X7,X7)))
      | v2_struct_0(X6)
      | ~ r2_hidden(X7,u1_struct_0(X6))
      | ~ l1_pre_topc(X6) ) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ r2_hidden(X7,u1_struct_0(X6))
      | l1_pre_topc(sK4(X6,k2_tarski(X7,X7)))
      | ~ l1_pre_topc(X6) ) ),
    inference(resolution,[],[f218,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f555,plain,
    ( ~ l1_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f553])).

fof(f553,plain,
    ( spl6_28
  <=> l1_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f660,plain,
    ( ~ spl6_1
    | ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f658,f126])).

fof(f658,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f657,f64])).

fof(f657,plain,
    ( v2_struct_0(sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f654,f66])).

fof(f654,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_27 ),
    inference(resolution,[],[f551,f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK4(X0,k2_tarski(X1,X1)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f197,f100])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK4(X0,k2_tarski(X1,X1)))
      | v1_xboole_0(k2_tarski(X1,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f85,f101])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK4(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f551,plain,
    ( v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f549])).

fof(f629,plain,
    ( ~ spl6_1
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | ~ spl6_1
    | spl6_25 ),
    inference(subsumption_resolution,[],[f627,f66])).

fof(f627,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_1
    | spl6_25 ),
    inference(subsumption_resolution,[],[f626,f126])).

fof(f626,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | spl6_25 ),
    inference(subsumption_resolution,[],[f623,f64])).

fof(f623,plain,
    ( v2_struct_0(sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | spl6_25 ),
    inference(resolution,[],[f543,f231])).

fof(f543,plain,
    ( ~ l1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f541])).

fof(f592,plain,
    ( spl6_27
    | ~ spl6_36
    | spl6_37
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f528,f124,f590,f586,f549])).

fof(f528,plain,
    ( ! [X7] :
        ( v2_tex_2(k2_tarski(sK1,sK1),X7)
        | ~ v1_tdlat_3(sK4(sK0,k2_tarski(sK1,sK1)))
        | ~ m1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)),X7)
        | v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X7) )
    | ~ spl6_1 ),
    inference(superposition,[],[f112,f375])).

fof(f375,plain,
    ( k2_tarski(sK1,sK1) = u1_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f374,f64])).

fof(f374,plain,
    ( v2_struct_0(sK0)
    | k2_tarski(sK1,sK1) = u1_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f368,f66])).

fof(f368,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k2_tarski(sK1,sK1) = u1_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_1 ),
    inference(resolution,[],[f243,f126])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k2_tarski(X1,X1) = u1_struct_0(sK4(X0,k2_tarski(X1,X1))) ) ),
    inference(subsumption_resolution,[],[f238,f100])).

fof(f238,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = u1_struct_0(sK4(X0,k2_tarski(X1,X1)))
      | v1_xboole_0(k2_tarski(X1,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f88,f101])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK4(X0,X1)) = X1
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f77,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f568,plain,
    ( spl6_27
    | ~ spl6_28
    | spl6_29
    | spl6_31
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f523,f124,f566,f557,f553,f549])).

fof(f523,plain,
    ( ! [X2] :
        ( k2_tarski(sK1,sK1) != k6_domain_1(k2_tarski(sK1,sK1),X2)
        | v7_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))
        | ~ m1_subset_1(X2,k2_tarski(sK1,sK1))
        | ~ l1_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))
        | v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) )
    | ~ spl6_1 ),
    inference(superposition,[],[f81,f375])).

fof(f81,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
      | v7_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK3(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK3(X0))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_1)).

fof(f135,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f133,f64])).

fof(f133,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f132,f115])).

fof(f115,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f74,f66])).

fof(f132,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f130,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

% (23890)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% (23895)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f130,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f131,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f119,f128,f124])).

fof(f119,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f94,f67])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (23866)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.48  % (23874)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.48  % (23866)Refutation not found, incomplete strategy% (23866)------------------------------
% 0.20/0.48  % (23866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23866)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (23866)Memory used [KB]: 10746
% 0.20/0.48  % (23866)Time elapsed: 0.073 s
% 0.20/0.48  % (23866)------------------------------
% 0.20/0.48  % (23866)------------------------------
% 0.20/0.48  % (23874)Refutation not found, incomplete strategy% (23874)------------------------------
% 0.20/0.48  % (23874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23874)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (23874)Memory used [KB]: 1791
% 0.20/0.49  % (23874)Time elapsed: 0.075 s
% 0.20/0.49  % (23874)------------------------------
% 0.20/0.49  % (23874)------------------------------
% 0.20/0.51  % (23868)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (23858)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (23856)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (23857)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (23860)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (23859)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (23861)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (23870)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (23861)Refutation not found, incomplete strategy% (23861)------------------------------
% 0.20/0.54  % (23861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23861)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23861)Memory used [KB]: 1791
% 0.20/0.54  % (23861)Time elapsed: 0.127 s
% 0.20/0.54  % (23861)------------------------------
% 0.20/0.54  % (23861)------------------------------
% 0.20/0.54  % (23869)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (23878)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (23864)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (23871)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (23875)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (23872)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (23872)Refutation not found, incomplete strategy% (23872)------------------------------
% 0.20/0.54  % (23872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23872)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23872)Memory used [KB]: 10618
% 0.20/0.54  % (23872)Time elapsed: 0.134 s
% 0.20/0.54  % (23872)------------------------------
% 0.20/0.54  % (23872)------------------------------
% 0.20/0.54  % (23884)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (23883)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (23884)Refutation not found, incomplete strategy% (23884)------------------------------
% 0.20/0.55  % (23884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (23882)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (23880)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (23867)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (23876)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (23877)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (23865)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (23863)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (23885)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (23885)Refutation not found, incomplete strategy% (23885)------------------------------
% 0.20/0.55  % (23885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (23887)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 0.20/0.55  % (23885)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (23885)Memory used [KB]: 1663
% 0.20/0.55  % (23885)Time elapsed: 0.146 s
% 0.20/0.55  % (23885)------------------------------
% 0.20/0.55  % (23885)------------------------------
% 0.20/0.56  % (23873)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.56  % (23884)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (23884)Memory used [KB]: 10746
% 0.20/0.56  % (23884)Time elapsed: 0.140 s
% 0.20/0.56  % (23884)------------------------------
% 0.20/0.56  % (23884)------------------------------
% 0.20/0.56  % (23862)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (23879)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.56  % (23880)Refutation not found, incomplete strategy% (23880)------------------------------
% 0.20/0.56  % (23880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (23880)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (23880)Memory used [KB]: 10746
% 0.20/0.56  % (23880)Time elapsed: 0.160 s
% 0.20/0.56  % (23880)------------------------------
% 0.20/0.56  % (23880)------------------------------
% 0.20/0.56  % (23881)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  % (23883)Refutation not found, incomplete strategy% (23883)------------------------------
% 0.20/0.56  % (23883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (23883)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (23883)Memory used [KB]: 6268
% 0.20/0.56  % (23883)Time elapsed: 0.155 s
% 0.20/0.56  % (23883)------------------------------
% 0.20/0.56  % (23883)------------------------------
% 0.20/0.56  % (23882)Refutation not found, incomplete strategy% (23882)------------------------------
% 0.20/0.56  % (23882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (23882)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (23882)Memory used [KB]: 6268
% 0.20/0.56  % (23882)Time elapsed: 0.153 s
% 0.20/0.56  % (23882)------------------------------
% 0.20/0.56  % (23882)------------------------------
% 0.20/0.56  % (23879)Refutation not found, incomplete strategy% (23879)------------------------------
% 0.20/0.56  % (23879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (23879)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (23879)Memory used [KB]: 10874
% 0.20/0.56  % (23879)Time elapsed: 0.160 s
% 0.20/0.56  % (23879)------------------------------
% 0.20/0.56  % (23879)------------------------------
% 0.20/0.57  % (23886)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.13/0.66  % (23862)Refutation found. Thanks to Tanya!
% 2.13/0.66  % SZS status Theorem for theBenchmark
% 2.13/0.66  % SZS output start Proof for theBenchmark
% 2.13/0.66  fof(f1823,plain,(
% 2.13/0.66    $false),
% 2.13/0.66    inference(avatar_sat_refutation,[],[f131,f135,f568,f592,f629,f660,f671,f696,f711,f945,f1820])).
% 2.13/0.66  fof(f1820,plain,(
% 2.13/0.66    ~spl6_1 | spl6_2 | ~spl6_37),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f1819])).
% 2.13/0.66  fof(f1819,plain,(
% 2.13/0.66    $false | (~spl6_1 | spl6_2 | ~spl6_37)),
% 2.13/0.66    inference(subsumption_resolution,[],[f1818,f126])).
% 2.13/0.66  fof(f126,plain,(
% 2.13/0.66    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl6_1),
% 2.13/0.66    inference(avatar_component_clause,[],[f124])).
% 2.13/0.66  fof(f124,plain,(
% 2.13/0.66    spl6_1 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.13/0.66  fof(f1818,plain,(
% 2.13/0.66    ~r2_hidden(sK1,u1_struct_0(sK0)) | (spl6_2 | ~spl6_37)),
% 2.13/0.66    inference(subsumption_resolution,[],[f1817,f160])).
% 2.13/0.66  fof(f160,plain,(
% 2.13/0.66    ~v2_tex_2(k2_tarski(sK1,sK1),sK0) | spl6_2),
% 2.13/0.66    inference(backward_demodulation,[],[f68,f158])).
% 2.13/0.66  fof(f158,plain,(
% 2.13/0.66    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | spl6_2),
% 2.13/0.66    inference(subsumption_resolution,[],[f153,f129])).
% 2.13/0.66  fof(f129,plain,(
% 2.13/0.66    ~v1_xboole_0(u1_struct_0(sK0)) | spl6_2),
% 2.13/0.66    inference(avatar_component_clause,[],[f128])).
% 2.13/0.66  fof(f128,plain,(
% 2.13/0.66    spl6_2 <=> v1_xboole_0(u1_struct_0(sK0))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.13/0.66  fof(f153,plain,(
% 2.13/0.66    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 2.13/0.66    inference(resolution,[],[f102,f67])).
% 2.13/0.66  fof(f67,plain,(
% 2.13/0.66    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.13/0.66    inference(cnf_transformation,[],[f48])).
% 2.13/0.66  fof(f48,plain,(
% 2.13/0.66    (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.13/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f47,f46])).
% 2.13/0.66  fof(f46,plain,(
% 2.13/0.66    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.13/0.66    introduced(choice_axiom,[])).
% 2.13/0.66  fof(f47,plain,(
% 2.13/0.66    ? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 2.13/0.66    introduced(choice_axiom,[])).
% 2.13/0.66  fof(f22,plain,(
% 2.13/0.66    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/0.66    inference(flattening,[],[f21])).
% 2.13/0.66  fof(f21,plain,(
% 2.13/0.66    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f20])).
% 2.13/0.66  fof(f20,negated_conjecture,(
% 2.13/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.13/0.66    inference(negated_conjecture,[],[f19])).
% 2.13/0.66  fof(f19,conjecture,(
% 2.13/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 2.13/0.66  fof(f102,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 2.13/0.66    inference(definition_unfolding,[],[f95,f70])).
% 2.13/0.66  fof(f70,plain,(
% 2.13/0.66    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f2])).
% 2.13/0.66  fof(f2,axiom,(
% 2.13/0.66    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.13/0.66  fof(f95,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f45])).
% 2.13/0.66  fof(f45,plain,(
% 2.13/0.66    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.13/0.66    inference(flattening,[],[f44])).
% 2.13/0.66  fof(f44,plain,(
% 2.13/0.66    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f11])).
% 2.13/0.66  fof(f11,axiom,(
% 2.13/0.66    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 2.13/0.66  fof(f68,plain,(
% 2.13/0.66    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 2.13/0.66    inference(cnf_transformation,[],[f48])).
% 2.13/0.66  fof(f1817,plain,(
% 2.13/0.66    v2_tex_2(k2_tarski(sK1,sK1),sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~spl6_37),
% 2.13/0.66    inference(subsumption_resolution,[],[f1816,f66])).
% 2.13/0.66  fof(f66,plain,(
% 2.13/0.66    l1_pre_topc(sK0)),
% 2.13/0.66    inference(cnf_transformation,[],[f48])).
% 2.13/0.66  fof(f1816,plain,(
% 2.13/0.66    ~l1_pre_topc(sK0) | v2_tex_2(k2_tarski(sK1,sK1),sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~spl6_37),
% 2.13/0.66    inference(subsumption_resolution,[],[f1815,f64])).
% 2.13/0.66  fof(f64,plain,(
% 2.13/0.66    ~v2_struct_0(sK0)),
% 2.13/0.66    inference(cnf_transformation,[],[f48])).
% 2.13/0.66  fof(f1815,plain,(
% 2.13/0.66    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_tex_2(k2_tarski(sK1,sK1),sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~spl6_37),
% 2.13/0.66    inference(duplicate_literal_removal,[],[f1810])).
% 2.13/0.66  fof(f1810,plain,(
% 2.13/0.66    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_tex_2(k2_tarski(sK1,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~spl6_37),
% 2.13/0.66    inference(resolution,[],[f591,f218])).
% 2.13/0.66  fof(f218,plain,(
% 2.13/0.66    ( ! [X0,X1] : (m1_pre_topc(sK4(X0,k2_tarski(X1,X1)),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~r2_hidden(X1,u1_struct_0(X0))) )),
% 2.13/0.66    inference(subsumption_resolution,[],[f214,f100])).
% 2.13/0.66  fof(f100,plain,(
% 2.13/0.66    ( ! [X0] : (~v1_xboole_0(k2_tarski(X0,X0))) )),
% 2.13/0.66    inference(definition_unfolding,[],[f69,f70])).
% 2.13/0.66  fof(f69,plain,(
% 2.13/0.66    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.13/0.66    inference(cnf_transformation,[],[f3])).
% 2.13/0.66  fof(f3,axiom,(
% 2.13/0.66    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 2.13/0.66  fof(f214,plain,(
% 2.13/0.66    ( ! [X0,X1] : (m1_pre_topc(sK4(X0,k2_tarski(X1,X1)),X0) | v1_xboole_0(k2_tarski(X1,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~r2_hidden(X1,u1_struct_0(X0))) )),
% 2.13/0.66    inference(resolution,[],[f87,f101])).
% 2.13/0.66  fof(f101,plain,(
% 2.13/0.66    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.13/0.66    inference(definition_unfolding,[],[f93,f70])).
% 2.13/0.66  fof(f93,plain,(
% 2.13/0.66    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f41])).
% 2.13/0.66  fof(f41,plain,(
% 2.13/0.66    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.13/0.66    inference(ennf_transformation,[],[f4])).
% 2.13/0.66  fof(f4,axiom,(
% 2.13/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 2.13/0.66  fof(f87,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK4(X0,X1),X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f58])).
% 2.13/0.66  fof(f58,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : ((u1_struct_0(sK4(X0,X1)) = X1 & m1_pre_topc(sK4(X0,X1),X0) & v1_pre_topc(sK4(X0,X1)) & ~v2_struct_0(sK4(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f57])).
% 2.13/0.66  fof(f57,plain,(
% 2.13/0.66    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK4(X0,X1)) = X1 & m1_pre_topc(sK4(X0,X1),X0) & v1_pre_topc(sK4(X0,X1)) & ~v2_struct_0(sK4(X0,X1))))),
% 2.13/0.66    introduced(choice_axiom,[])).
% 2.13/0.66  fof(f35,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.66    inference(flattening,[],[f34])).
% 2.13/0.66  fof(f34,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f17])).
% 2.13/0.66  fof(f17,axiom,(
% 2.13/0.66    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 2.13/0.66  fof(f591,plain,(
% 2.13/0.66    ( ! [X7] : (~m1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)),X7) | v2_struct_0(X7) | ~l1_pre_topc(X7) | v2_tex_2(k2_tarski(sK1,sK1),X7)) ) | ~spl6_37),
% 2.13/0.66    inference(avatar_component_clause,[],[f590])).
% 2.13/0.66  fof(f590,plain,(
% 2.13/0.66    spl6_37 <=> ! [X7] : (v2_tex_2(k2_tarski(sK1,sK1),X7) | v2_struct_0(X7) | ~l1_pre_topc(X7) | ~m1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)),X7))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 2.13/0.66  fof(f945,plain,(
% 2.13/0.66    ~spl6_31),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f944])).
% 2.13/0.66  fof(f944,plain,(
% 2.13/0.66    $false | ~spl6_31),
% 2.13/0.66    inference(subsumption_resolution,[],[f943,f116])).
% 2.13/0.66  fof(f116,plain,(
% 2.13/0.66    ( ! [X0] : (m1_subset_1(X0,k2_tarski(X0,X0))) )),
% 2.13/0.66    inference(resolution,[],[f92,f110])).
% 2.13/0.66  fof(f110,plain,(
% 2.13/0.66    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 2.13/0.66    inference(equality_resolution,[],[f109])).
% 2.13/0.66  fof(f109,plain,(
% 2.13/0.66    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 2.13/0.66    inference(equality_resolution,[],[f105])).
% 2.13/0.66  fof(f105,plain,(
% 2.13/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 2.13/0.66    inference(definition_unfolding,[],[f97,f70])).
% 2.13/0.66  fof(f97,plain,(
% 2.13/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.13/0.66    inference(cnf_transformation,[],[f63])).
% 2.13/0.66  fof(f63,plain,(
% 2.13/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.13/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f61,f62])).
% 2.13/0.66  fof(f62,plain,(
% 2.13/0.66    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 2.13/0.66    introduced(choice_axiom,[])).
% 2.13/0.66  fof(f61,plain,(
% 2.13/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.13/0.66    inference(rectify,[],[f60])).
% 2.13/0.66  fof(f60,plain,(
% 2.13/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.13/0.66    inference(nnf_transformation,[],[f1])).
% 2.13/0.66  fof(f1,axiom,(
% 2.13/0.66    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.13/0.66  fof(f92,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f40])).
% 2.13/0.66  fof(f40,plain,(
% 2.13/0.66    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.13/0.66    inference(ennf_transformation,[],[f5])).
% 2.13/0.66  fof(f5,axiom,(
% 2.13/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 2.13/0.66  fof(f943,plain,(
% 2.13/0.66    ~m1_subset_1(sK1,k2_tarski(sK1,sK1)) | ~spl6_31),
% 2.13/0.66    inference(trivial_inequality_removal,[],[f942])).
% 2.13/0.66  fof(f942,plain,(
% 2.13/0.66    k2_tarski(sK1,sK1) != k2_tarski(sK1,sK1) | ~m1_subset_1(sK1,k2_tarski(sK1,sK1)) | ~spl6_31),
% 2.13/0.66    inference(superposition,[],[f567,f157])).
% 2.13/0.66  fof(f157,plain,(
% 2.13/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k6_domain_1(k2_tarski(X0,X0),X0)) )),
% 2.13/0.66    inference(subsumption_resolution,[],[f150,f100])).
% 2.13/0.66  fof(f150,plain,(
% 2.13/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k6_domain_1(k2_tarski(X0,X0),X0) | v1_xboole_0(k2_tarski(X0,X0))) )),
% 2.13/0.66    inference(resolution,[],[f102,f116])).
% 2.13/0.66  fof(f567,plain,(
% 2.13/0.66    ( ! [X2] : (k2_tarski(sK1,sK1) != k6_domain_1(k2_tarski(sK1,sK1),X2) | ~m1_subset_1(X2,k2_tarski(sK1,sK1))) ) | ~spl6_31),
% 2.13/0.66    inference(avatar_component_clause,[],[f566])).
% 2.13/0.66  fof(f566,plain,(
% 2.13/0.66    spl6_31 <=> ! [X2] : (k2_tarski(sK1,sK1) != k6_domain_1(k2_tarski(sK1,sK1),X2) | ~m1_subset_1(X2,k2_tarski(sK1,sK1)))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 2.13/0.66  fof(f711,plain,(
% 2.13/0.66    ~spl6_1 | spl6_47),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f710])).
% 2.13/0.66  fof(f710,plain,(
% 2.13/0.66    $false | (~spl6_1 | spl6_47)),
% 2.13/0.66    inference(subsumption_resolution,[],[f709,f65])).
% 2.13/0.66  fof(f65,plain,(
% 2.13/0.66    v2_pre_topc(sK0)),
% 2.13/0.66    inference(cnf_transformation,[],[f48])).
% 2.13/0.66  fof(f709,plain,(
% 2.13/0.66    ~v2_pre_topc(sK0) | (~spl6_1 | spl6_47)),
% 2.13/0.66    inference(subsumption_resolution,[],[f708,f66])).
% 2.13/0.66  fof(f708,plain,(
% 2.13/0.66    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | spl6_47)),
% 2.13/0.66    inference(subsumption_resolution,[],[f707,f126])).
% 2.13/0.66  fof(f707,plain,(
% 2.13/0.66    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl6_47),
% 2.13/0.66    inference(subsumption_resolution,[],[f704,f64])).
% 2.13/0.66  fof(f704,plain,(
% 2.13/0.66    v2_struct_0(sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl6_47),
% 2.13/0.66    inference(resolution,[],[f692,f232])).
% 2.13/0.66  fof(f232,plain,(
% 2.13/0.66    ( ! [X4,X5] : (v2_pre_topc(sK4(X4,k2_tarski(X5,X5))) | v2_struct_0(X4) | ~r2_hidden(X5,u1_struct_0(X4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4)) )),
% 2.13/0.66    inference(duplicate_literal_removal,[],[f229])).
% 2.13/0.66  fof(f229,plain,(
% 2.13/0.66    ( ! [X4,X5] : (~l1_pre_topc(X4) | v2_struct_0(X4) | ~r2_hidden(X5,u1_struct_0(X4)) | v2_pre_topc(sK4(X4,k2_tarski(X5,X5))) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4)) )),
% 2.13/0.66    inference(resolution,[],[f218,f91])).
% 2.13/0.66  fof(f91,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f39])).
% 2.13/0.66  fof(f39,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.13/0.66    inference(flattening,[],[f38])).
% 2.13/0.66  fof(f38,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f7])).
% 2.13/0.66  fof(f7,axiom,(
% 2.13/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.13/0.66  fof(f692,plain,(
% 2.13/0.66    ~v2_pre_topc(sK4(sK0,k2_tarski(sK1,sK1))) | spl6_47),
% 2.13/0.66    inference(avatar_component_clause,[],[f690])).
% 2.13/0.66  fof(f690,plain,(
% 2.13/0.66    spl6_47 <=> v2_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 2.13/0.66  fof(f696,plain,(
% 2.13/0.66    spl6_36 | ~spl6_47 | ~spl6_25 | spl6_27 | ~spl6_29),
% 2.13/0.66    inference(avatar_split_clause,[],[f695,f557,f549,f541,f690,f586])).
% 2.13/0.66  fof(f586,plain,(
% 2.13/0.66    spl6_36 <=> v1_tdlat_3(sK4(sK0,k2_tarski(sK1,sK1)))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 2.13/0.66  fof(f541,plain,(
% 2.13/0.66    spl6_25 <=> l1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 2.13/0.66  fof(f549,plain,(
% 2.13/0.66    spl6_27 <=> v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.13/0.66  fof(f557,plain,(
% 2.13/0.66    spl6_29 <=> v7_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.13/0.66  fof(f695,plain,(
% 2.13/0.66    ~v2_pre_topc(sK4(sK0,k2_tarski(sK1,sK1))) | v1_tdlat_3(sK4(sK0,k2_tarski(sK1,sK1))) | (~spl6_25 | spl6_27 | ~spl6_29)),
% 2.13/0.66    inference(subsumption_resolution,[],[f694,f542])).
% 2.13/0.66  fof(f542,plain,(
% 2.13/0.66    l1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1))) | ~spl6_25),
% 2.13/0.66    inference(avatar_component_clause,[],[f541])).
% 2.13/0.66  fof(f694,plain,(
% 2.13/0.66    ~v2_pre_topc(sK4(sK0,k2_tarski(sK1,sK1))) | v1_tdlat_3(sK4(sK0,k2_tarski(sK1,sK1))) | ~l1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1))) | (spl6_27 | ~spl6_29)),
% 2.13/0.66    inference(subsumption_resolution,[],[f676,f550])).
% 2.13/0.66  fof(f550,plain,(
% 2.13/0.66    ~v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) | spl6_27),
% 2.13/0.66    inference(avatar_component_clause,[],[f549])).
% 2.13/0.66  fof(f676,plain,(
% 2.13/0.66    ~v2_pre_topc(sK4(sK0,k2_tarski(sK1,sK1))) | v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) | v1_tdlat_3(sK4(sK0,k2_tarski(sK1,sK1))) | ~l1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1))) | ~spl6_29),
% 2.13/0.66    inference(resolution,[],[f558,f188])).
% 2.13/0.66  fof(f188,plain,(
% 2.13/0.66    ( ! [X0] : (~v7_struct_0(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 2.13/0.66    inference(duplicate_literal_removal,[],[f187])).
% 2.13/0.66  fof(f187,plain,(
% 2.13/0.66    ( ! [X0] : (~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.13/0.66    inference(resolution,[],[f83,f75])).
% 2.13/0.66  fof(f75,plain,(
% 2.13/0.66    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f25])).
% 2.13/0.66  fof(f25,plain,(
% 2.13/0.66    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.13/0.66    inference(ennf_transformation,[],[f13])).
% 2.13/0.66  fof(f13,axiom,(
% 2.13/0.66    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.13/0.66  fof(f83,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | v1_tdlat_3(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f33])).
% 2.13/0.66  fof(f33,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : ((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.66    inference(flattening,[],[f32])).
% 2.13/0.66  fof(f32,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : (((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f14])).
% 2.13/0.66  fof(f14,axiom,(
% 2.13/0.66    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).
% 2.13/0.66  fof(f558,plain,(
% 2.13/0.66    v7_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) | ~spl6_29),
% 2.13/0.66    inference(avatar_component_clause,[],[f557])).
% 2.13/0.66  fof(f671,plain,(
% 2.13/0.66    ~spl6_1 | spl6_28),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f670])).
% 2.13/0.66  fof(f670,plain,(
% 2.13/0.66    $false | (~spl6_1 | spl6_28)),
% 2.13/0.66    inference(subsumption_resolution,[],[f669,f64])).
% 2.13/0.66  fof(f669,plain,(
% 2.13/0.66    v2_struct_0(sK0) | (~spl6_1 | spl6_28)),
% 2.13/0.66    inference(subsumption_resolution,[],[f668,f66])).
% 2.13/0.66  fof(f668,plain,(
% 2.13/0.66    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_1 | spl6_28)),
% 2.13/0.66    inference(subsumption_resolution,[],[f665,f126])).
% 2.13/0.66  fof(f665,plain,(
% 2.13/0.66    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl6_28),
% 2.13/0.66    inference(resolution,[],[f555,f237])).
% 2.13/0.66  fof(f237,plain,(
% 2.13/0.66    ( ! [X0,X1] : (l1_struct_0(sK4(X0,k2_tarski(X1,X1))) | ~r2_hidden(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.66    inference(resolution,[],[f231,f74])).
% 2.13/0.66  fof(f74,plain,(
% 2.13/0.66    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f24])).
% 2.13/0.66  fof(f24,plain,(
% 2.13/0.66    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.13/0.66    inference(ennf_transformation,[],[f8])).
% 2.13/0.66  fof(f8,axiom,(
% 2.13/0.66    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.13/0.66  fof(f231,plain,(
% 2.13/0.66    ( ! [X6,X7] : (l1_pre_topc(sK4(X6,k2_tarski(X7,X7))) | v2_struct_0(X6) | ~r2_hidden(X7,u1_struct_0(X6)) | ~l1_pre_topc(X6)) )),
% 2.13/0.66    inference(duplicate_literal_removal,[],[f230])).
% 2.13/0.66  fof(f230,plain,(
% 2.13/0.66    ( ! [X6,X7] : (~l1_pre_topc(X6) | v2_struct_0(X6) | ~r2_hidden(X7,u1_struct_0(X6)) | l1_pre_topc(sK4(X6,k2_tarski(X7,X7))) | ~l1_pre_topc(X6)) )),
% 2.13/0.66    inference(resolution,[],[f218,f76])).
% 2.13/0.66  fof(f76,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f26])).
% 2.13/0.66  fof(f26,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/0.66    inference(ennf_transformation,[],[f9])).
% 2.13/0.66  fof(f9,axiom,(
% 2.13/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.13/0.66  fof(f555,plain,(
% 2.13/0.66    ~l1_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) | spl6_28),
% 2.13/0.66    inference(avatar_component_clause,[],[f553])).
% 2.13/0.66  fof(f553,plain,(
% 2.13/0.66    spl6_28 <=> l1_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.13/0.66  fof(f660,plain,(
% 2.13/0.66    ~spl6_1 | ~spl6_27),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f659])).
% 2.13/0.66  fof(f659,plain,(
% 2.13/0.66    $false | (~spl6_1 | ~spl6_27)),
% 2.13/0.66    inference(subsumption_resolution,[],[f658,f126])).
% 2.13/0.66  fof(f658,plain,(
% 2.13/0.66    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~spl6_27),
% 2.13/0.66    inference(subsumption_resolution,[],[f657,f64])).
% 2.13/0.66  fof(f657,plain,(
% 2.13/0.66    v2_struct_0(sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~spl6_27),
% 2.13/0.66    inference(subsumption_resolution,[],[f654,f66])).
% 2.13/0.66  fof(f654,plain,(
% 2.13/0.66    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~spl6_27),
% 2.13/0.66    inference(resolution,[],[f551,f201])).
% 2.13/0.66  fof(f201,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~v2_struct_0(sK4(X0,k2_tarski(X1,X1))) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~r2_hidden(X1,u1_struct_0(X0))) )),
% 2.13/0.66    inference(subsumption_resolution,[],[f197,f100])).
% 2.13/0.66  fof(f197,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~v2_struct_0(sK4(X0,k2_tarski(X1,X1))) | v1_xboole_0(k2_tarski(X1,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~r2_hidden(X1,u1_struct_0(X0))) )),
% 2.13/0.66    inference(resolution,[],[f85,f101])).
% 2.13/0.66  fof(f85,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(sK4(X0,X1)) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f58])).
% 2.13/0.66  fof(f551,plain,(
% 2.13/0.66    v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) | ~spl6_27),
% 2.13/0.66    inference(avatar_component_clause,[],[f549])).
% 2.13/0.66  fof(f629,plain,(
% 2.13/0.66    ~spl6_1 | spl6_25),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f628])).
% 2.13/0.66  fof(f628,plain,(
% 2.13/0.66    $false | (~spl6_1 | spl6_25)),
% 2.13/0.66    inference(subsumption_resolution,[],[f627,f66])).
% 2.13/0.66  fof(f627,plain,(
% 2.13/0.66    ~l1_pre_topc(sK0) | (~spl6_1 | spl6_25)),
% 2.13/0.66    inference(subsumption_resolution,[],[f626,f126])).
% 2.13/0.66  fof(f626,plain,(
% 2.13/0.66    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | spl6_25),
% 2.13/0.66    inference(subsumption_resolution,[],[f623,f64])).
% 2.13/0.66  fof(f623,plain,(
% 2.13/0.66    v2_struct_0(sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | spl6_25),
% 2.13/0.66    inference(resolution,[],[f543,f231])).
% 2.13/0.66  fof(f543,plain,(
% 2.13/0.66    ~l1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1))) | spl6_25),
% 2.13/0.66    inference(avatar_component_clause,[],[f541])).
% 2.13/0.66  fof(f592,plain,(
% 2.13/0.66    spl6_27 | ~spl6_36 | spl6_37 | ~spl6_1),
% 2.13/0.66    inference(avatar_split_clause,[],[f528,f124,f590,f586,f549])).
% 2.13/0.66  fof(f528,plain,(
% 2.13/0.66    ( ! [X7] : (v2_tex_2(k2_tarski(sK1,sK1),X7) | ~v1_tdlat_3(sK4(sK0,k2_tarski(sK1,sK1))) | ~m1_pre_topc(sK4(sK0,k2_tarski(sK1,sK1)),X7) | v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) | ~l1_pre_topc(X7) | v2_struct_0(X7)) ) | ~spl6_1),
% 2.13/0.66    inference(superposition,[],[f112,f375])).
% 2.13/0.66  fof(f375,plain,(
% 2.13/0.66    k2_tarski(sK1,sK1) = u1_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) | ~spl6_1),
% 2.13/0.66    inference(subsumption_resolution,[],[f374,f64])).
% 2.13/0.66  fof(f374,plain,(
% 2.13/0.66    v2_struct_0(sK0) | k2_tarski(sK1,sK1) = u1_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) | ~spl6_1),
% 2.13/0.66    inference(subsumption_resolution,[],[f368,f66])).
% 2.13/0.66  fof(f368,plain,(
% 2.13/0.66    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k2_tarski(sK1,sK1) = u1_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) | ~spl6_1),
% 2.13/0.66    inference(resolution,[],[f243,f126])).
% 2.13/0.66  fof(f243,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~r2_hidden(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k2_tarski(X1,X1) = u1_struct_0(sK4(X0,k2_tarski(X1,X1)))) )),
% 2.13/0.66    inference(subsumption_resolution,[],[f238,f100])).
% 2.13/0.66  fof(f238,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k2_tarski(X1,X1) = u1_struct_0(sK4(X0,k2_tarski(X1,X1))) | v1_xboole_0(k2_tarski(X1,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~r2_hidden(X1,u1_struct_0(X0))) )),
% 2.13/0.66    inference(resolution,[],[f88,f101])).
% 2.13/0.66  fof(f88,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK4(X0,X1)) = X1 | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f58])).
% 2.13/0.66  fof(f112,plain,(
% 2.13/0.66    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.66    inference(global_subsumption,[],[f77,f107])).
% 2.13/0.66  fof(f107,plain,(
% 2.13/0.66    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.66    inference(equality_resolution,[],[f90])).
% 2.13/0.66  fof(f90,plain,(
% 2.13/0.66    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f59])).
% 2.13/0.66  fof(f59,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.66    inference(nnf_transformation,[],[f37])).
% 2.13/0.66  fof(f37,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.66    inference(flattening,[],[f36])).
% 2.13/0.66  fof(f36,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f18])).
% 2.13/0.66  fof(f18,axiom,(
% 2.13/0.66    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 2.13/0.66  fof(f77,plain,(
% 2.13/0.66    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f27])).
% 2.13/0.66  fof(f27,plain,(
% 2.13/0.66    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/0.66    inference(ennf_transformation,[],[f12])).
% 2.13/0.66  fof(f12,axiom,(
% 2.13/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.13/0.66  fof(f568,plain,(
% 2.13/0.66    spl6_27 | ~spl6_28 | spl6_29 | spl6_31 | ~spl6_1),
% 2.13/0.66    inference(avatar_split_clause,[],[f523,f124,f566,f557,f553,f549])).
% 2.13/0.66  fof(f523,plain,(
% 2.13/0.66    ( ! [X2] : (k2_tarski(sK1,sK1) != k6_domain_1(k2_tarski(sK1,sK1),X2) | v7_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,k2_tarski(sK1,sK1)) | ~l1_struct_0(sK4(sK0,k2_tarski(sK1,sK1))) | v2_struct_0(sK4(sK0,k2_tarski(sK1,sK1)))) ) | ~spl6_1),
% 2.13/0.66    inference(superposition,[],[f81,f375])).
% 2.13/0.66  fof(f81,plain,(
% 2.13/0.66    ( ! [X0,X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | v7_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f56])).
% 2.13/0.66  fof(f56,plain,(
% 2.13/0.66    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK3(X0)) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.13/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).
% 2.13/0.66  fof(f55,plain,(
% 2.13/0.66    ! [X0] : (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK3(X0)) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 2.13/0.66    introduced(choice_axiom,[])).
% 2.13/0.66  fof(f54,plain,(
% 2.13/0.66    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.13/0.66    inference(rectify,[],[f53])).
% 2.13/0.66  fof(f53,plain,(
% 2.13/0.66    ! [X0] : (((v7_struct_0(X0) | ! [X1] : (u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~v7_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.13/0.66    inference(nnf_transformation,[],[f31])).
% 2.13/0.66  fof(f31,plain,(
% 2.13/0.66    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.13/0.66    inference(flattening,[],[f30])).
% 2.13/0.66  fof(f30,plain,(
% 2.13/0.66    ! [X0] : ((v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f15])).
% 2.13/0.66  fof(f15,axiom,(
% 2.13/0.66    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_struct_0(X0) <=> ? [X1] : (u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_1)).
% 2.13/0.66  fof(f135,plain,(
% 2.13/0.66    ~spl6_2),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f134])).
% 2.13/0.66  fof(f134,plain,(
% 2.13/0.66    $false | ~spl6_2),
% 2.13/0.66    inference(subsumption_resolution,[],[f133,f64])).
% 2.13/0.66  fof(f133,plain,(
% 2.13/0.66    v2_struct_0(sK0) | ~spl6_2),
% 2.13/0.66    inference(subsumption_resolution,[],[f132,f115])).
% 2.13/0.66  fof(f115,plain,(
% 2.13/0.66    l1_struct_0(sK0)),
% 2.13/0.66    inference(resolution,[],[f74,f66])).
% 2.13/0.66  fof(f132,plain,(
% 2.13/0.66    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_2),
% 2.13/0.66    inference(resolution,[],[f130,f78])).
% 2.13/0.66  fof(f78,plain,(
% 2.13/0.66    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f29])).
% 2.13/0.66  fof(f29,plain,(
% 2.13/0.66    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.13/0.66    inference(flattening,[],[f28])).
% 2.13/0.66  fof(f28,plain,(
% 2.13/0.66    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f10])).
% 2.13/0.67  % (23890)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.13/0.67  % (23895)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.13/0.67  fof(f10,axiom,(
% 2.13/0.67    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 2.13/0.67  fof(f130,plain,(
% 2.13/0.67    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_2),
% 2.13/0.67    inference(avatar_component_clause,[],[f128])).
% 2.13/0.67  fof(f131,plain,(
% 2.13/0.67    spl6_1 | spl6_2),
% 2.13/0.67    inference(avatar_split_clause,[],[f119,f128,f124])).
% 2.13/0.67  fof(f119,plain,(
% 2.13/0.67    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0))),
% 2.13/0.67    inference(resolution,[],[f94,f67])).
% 2.13/0.67  fof(f94,plain,(
% 2.13/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.13/0.67    inference(cnf_transformation,[],[f43])).
% 2.13/0.67  fof(f43,plain,(
% 2.13/0.67    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.13/0.67    inference(flattening,[],[f42])).
% 2.13/0.67  fof(f42,plain,(
% 2.13/0.67    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.13/0.67    inference(ennf_transformation,[],[f6])).
% 2.13/0.67  fof(f6,axiom,(
% 2.13/0.67    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 2.13/0.67  % SZS output end Proof for theBenchmark
% 2.13/0.67  % (23862)------------------------------
% 2.13/0.67  % (23862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.67  % (23862)Termination reason: Refutation
% 2.13/0.67  
% 2.13/0.67  % (23862)Memory used [KB]: 11641
% 2.13/0.67  % (23862)Time elapsed: 0.237 s
% 2.13/0.67  % (23862)------------------------------
% 2.13/0.67  % (23862)------------------------------
% 2.13/0.67  % (23855)Success in time 0.313 s
%------------------------------------------------------------------------------
