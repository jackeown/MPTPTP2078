%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0371+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:51 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 100 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  187 ( 371 expanded)
%              Number of equality atoms :   23 (  51 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f25,f30,f53,f57,f68,f71])).

fof(f71,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f61,f67])).

fof(f67,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_6
  <=> r2_hidden(sK3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f61,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_5 ),
    inference(subsumption_resolution,[],[f60,f29])).

fof(f29,plain,
    ( sK1 != k3_subset_1(sK0,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl4_3
  <=> sK1 = k3_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f60,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | sK1 = k3_subset_1(sK0,sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_5 ),
    inference(subsumption_resolution,[],[f58,f19])).

fof(f19,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f58,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sK1 = k3_subset_1(sK0,sK2)
    | ~ spl4_2
    | spl4_5 ),
    inference(resolution,[],[f52,f34])).

fof(f34,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,sK1,X0),sK1)
        | ~ r2_hidden(sK3(sK0,sK1,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | sK1 = k3_subset_1(sK0,X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f24,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k3_subset_1(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_subset_1)).

fof(f24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f52,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_5
  <=> r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( spl4_6
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f62,f50,f46,f65])).

fof(f46,plain,
    ( spl4_4
  <=> m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f62,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f59,f47])).

fof(f47,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f59,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | spl4_5 ),
    inference(resolution,[],[f52,f9])).

fof(f9,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( ~ r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( ~ r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_subset_1)).

fof(f57,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f55,f29])).

fof(f55,plain,
    ( sK1 = k3_subset_1(sK0,sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f54,f19])).

fof(f54,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sK1 = k3_subset_1(sK0,sK2)
    | ~ spl4_2
    | spl4_4 ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(sK0,sK1,X2),sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | sK1 = k3_subset_1(sK0,X2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f24,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | k3_subset_1(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f53,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f44,f27,f22,f17,f50,f46])).

fof(f44,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f43,f29])).

fof(f43,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | sK1 = k3_subset_1(sK0,sK2)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f42,f19])).

fof(f42,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | sK1 = k3_subset_1(sK0,sK2)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | sK1 = k3_subset_1(sK0,sK2)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f35,f8])).

% (27567)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f8,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK0,sK1,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK3(sK0,sK1,X1),sK1)
        | sK1 = k3_subset_1(sK0,X1) )
    | ~ spl4_2 ),
    inference(resolution,[],[f24,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k3_subset_1(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f11,f27])).

fof(f11,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f25,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f12,f22])).

fof(f12,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f20,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f10,f17])).

fof(f10,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
