%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 121 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  206 ( 427 expanded)
%              Number of equality atoms :   12 (  35 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f133,f144,f161,f184,f189,f210,f218])).

fof(f218,plain,
    ( spl8_23
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f216,f181,f186])).

fof(f186,plain,
    ( spl8_23
  <=> sP7(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f181,plain,
    ( spl8_22
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f216,plain,
    ( sP7(sK0)
    | ~ spl8_22 ),
    inference(resolution,[],[f183,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sP7(X0) ) ),
    inference(resolution,[],[f33,f100])).

fof(f100,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f99,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f99,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f33_D])).

fof(f33_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f183,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f181])).

fof(f210,plain,
    ( ~ spl8_19
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f207,f177,f141,f158])).

fof(f158,plain,
    ( spl8_19
  <=> sK4 = k1_funct_1(sK3,sK6(sK0,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f141,plain,
    ( spl8_16
  <=> r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f177,plain,
    ( spl8_21
  <=> m1_subset_1(sK6(sK0,sK2,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f207,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2)
    | sK4 != k1_funct_1(sK3,sK6(sK0,sK2,sK3,sK4))
    | ~ spl8_21 ),
    inference(resolution,[],[f179,f15])).

fof(f15,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f179,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3,sK4),sK0)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f177])).

fof(f189,plain,
    ( ~ spl8_23
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f175,f130,f186])).

fof(f130,plain,
    ( spl8_15
  <=> r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f175,plain,
    ( ~ sP7(sK0)
    | ~ spl8_15 ),
    inference(resolution,[],[f132,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f29,f33_D])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f132,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f184,plain,
    ( spl8_21
    | spl8_22
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f174,f130,f181,f177])).

fof(f174,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK3,sK4),sK0)
    | ~ spl8_15 ),
    inference(resolution,[],[f132,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f161,plain,
    ( spl8_19
    | ~ spl8_3
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f155,f51,f41,f36,f46,f158])).

fof(f46,plain,
    ( spl8_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f36,plain,
    ( spl8_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f41,plain,
    ( spl8_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f51,plain,
    ( spl8_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f155,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK6(sK0,sK2,sK3,sK4))
    | ~ spl8_4 ),
    inference(resolution,[],[f32,f53])).

fof(f53,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | k1_funct_1(X3,sK6(X0,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f144,plain,
    ( spl8_16
    | ~ spl8_3
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f138,f51,f41,f36,f46,f141])).

fof(f138,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2)
    | ~ spl8_4 ),
    inference(resolution,[],[f31,f53])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | r2_hidden(sK6(X0,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f133,plain,
    ( spl8_15
    | ~ spl8_3
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f127,f51,f41,f36,f46,f130])).

fof(f127,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f30,f53])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | r2_hidden(sK6(X0,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f16,f51])).

fof(f16,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f17,f46])).

fof(f17,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (12836)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.48  % (12844)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.48  % (12844)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f133,f144,f161,f184,f189,f210,f218])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    spl8_23 | ~spl8_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f216,f181,f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    spl8_23 <=> sP7(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    spl8_22 <=> v1_xboole_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    sP7(sK0) | ~spl8_22),
% 0.21/0.48    inference(resolution,[],[f183,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | sP7(X0)) )),
% 0.21/0.48    inference(resolution,[],[f33,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(resolution,[],[f99,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f26,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP7(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33_D])).
% 0.21/0.48  fof(f33_D,plain,(
% 0.21/0.48    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP7(X1)) )),
% 0.21/0.48    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    v1_xboole_0(sK0) | ~spl8_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f181])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    ~spl8_19 | ~spl8_16 | ~spl8_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f207,f177,f141,f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    spl8_19 <=> sK4 = k1_funct_1(sK3,sK6(sK0,sK2,sK3,sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl8_16 <=> r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    spl8_21 <=> m1_subset_1(sK6(sK0,sK2,sK3,sK4),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    ~r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2) | sK4 != k1_funct_1(sK3,sK6(sK0,sK2,sK3,sK4)) | ~spl8_21),
% 0.21/0.48    inference(resolution,[],[f179,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    m1_subset_1(sK6(sK0,sK2,sK3,sK4),sK0) | ~spl8_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f177])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ~spl8_23 | ~spl8_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f175,f130,f186])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    spl8_15 <=> r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ~sP7(sK0) | ~spl8_15),
% 0.21/0.48    inference(resolution,[],[f132,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP7(X1)) )),
% 0.21/0.48    inference(general_splitting,[],[f29,f33_D])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0) | ~spl8_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f130])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    spl8_21 | spl8_22 | ~spl8_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f174,f130,f181,f177])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    v1_xboole_0(sK0) | m1_subset_1(sK6(sK0,sK2,sK3,sK4),sK0) | ~spl8_15),
% 0.21/0.48    inference(resolution,[],[f132,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl8_19 | ~spl8_3 | ~spl8_1 | ~spl8_2 | ~spl8_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f155,f51,f41,f36,f46,f158])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl8_3 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl8_1 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl8_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl8_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~v1_funct_2(sK3,sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK6(sK0,sK2,sK3,sK4)) | ~spl8_4),
% 0.21/0.48    inference(resolution,[],[f32,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | k1_funct_1(X3,sK6(X0,X2,X3,X4)) = X4) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl8_16 | ~spl8_3 | ~spl8_1 | ~spl8_2 | ~spl8_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f138,f51,f41,f36,f46,f141])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ~v1_funct_2(sK3,sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | r2_hidden(sK6(sK0,sK2,sK3,sK4),sK2) | ~spl8_4),
% 0.21/0.48    inference(resolution,[],[f31,f53])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | r2_hidden(sK6(X0,X2,X3,X4),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    spl8_15 | ~spl8_3 | ~spl8_1 | ~spl8_2 | ~spl8_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f127,f51,f41,f36,f46,f130])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~v1_funct_2(sK3,sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | r2_hidden(sK6(sK0,sK2,sK3,sK4),sK0) | ~spl8_4),
% 0.21/0.48    inference(resolution,[],[f30,f53])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | r2_hidden(sK6(X0,X2,X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl8_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f51])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl8_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f46])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl8_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f41])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl8_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f36])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (12844)------------------------------
% 0.21/0.48  % (12844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12844)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (12844)Memory used [KB]: 10874
% 0.21/0.48  % (12844)Time elapsed: 0.080 s
% 0.21/0.48  % (12844)------------------------------
% 0.21/0.48  % (12844)------------------------------
% 0.21/0.49  % (12827)Success in time 0.129 s
%------------------------------------------------------------------------------
