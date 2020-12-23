%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 145 expanded)
%              Number of leaves         :   13 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  189 ( 400 expanded)
%              Number of equality atoms :    2 (  18 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f60,f83,f106,f109])).

fof(f109,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f107,f88])).

fof(f88,plain,
    ( m1_subset_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f48,f59,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
      | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f35,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f32,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_2)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f59,plain,
    ( m1_subset_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_3
  <=> m1_subset_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f48,plain,
    ( ! [X0] : ~ v1_xboole_0(k5_partfun1(X0,sK1,k3_partfun1(k1_xboole_0,X0,sK1)))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f41,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_funct_2)).

fof(f41,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

% (9967)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% (9963)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (9968)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f107,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_1
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f48,f46,f82,f105,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(sK2(X0,X1,X2))
      | ~ m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2(X0,X1,X2),X0,X1)
      | m1_funct_2(X2,X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ( ( ~ m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(sK2(X0,X1,X2),X0,X1)
              | ~ v1_funct_1(sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,X2) )
     => ( ( ~ m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(sK2(X0,X1,X2),X0,X1)
          | ~ v1_funct_1(sK2(X0,X1,X2)) )
        & m1_subset_1(sK2(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
              | ~ m1_subset_1(X3,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) ) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( m1_subset_1(X3,X2)
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).

fof(f105,plain,
    ( v1_funct_2(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_5
  <=> v1_funct_2(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f82,plain,
    ( v1_funct_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_4
  <=> v1_funct_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f46,plain,
    ( ~ m1_funct_2(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)),sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_2
  <=> m1_funct_2(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f106,plain,
    ( spl3_5
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f84,f57,f39,f103])).

fof(f84,plain,
    ( v1_funct_2(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),sK0,sK1)
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f48,f59,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
      | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
      | v1_funct_2(X0,X1,X2) ) ),
    inference(resolution,[],[f36,f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,
    ( spl3_4
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f72,f57,f39,f80])).

fof(f72,plain,
    ( v1_funct_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))))
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f48,f59,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
      | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
      | v1_funct_1(X0) ) ),
    inference(resolution,[],[f37,f24])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f30,f22])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,
    ( spl3_3
    | spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f51,f44,f39,f57])).

fof(f51,plain,
    ( m1_subset_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))
    | spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f48,f46,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),X2)
      | m1_funct_2(X2,X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f33,f44])).

fof(f33,plain,(
    ~ m1_funct_2(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)),sK0,sK1) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
        & ~ v1_xboole_0(X1) )
   => ( ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_funct_2)).

fof(f42,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (9972)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (9964)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (9972)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f42,f47,f60,f83,f106,f109])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    spl3_1 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    $false | (spl3_1 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.21/0.46    inference(subsumption_resolution,[],[f107,f88])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    m1_subset_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl3_1 | ~spl3_3)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f59,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.46    inference(resolution,[],[f35,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f32,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_2)).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    m1_subset_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl3_3 <=> m1_subset_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(k5_partfun1(X0,sK1,k3_partfun1(k1_xboole_0,X0,sK1)))) ) | spl3_1),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f41,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f23,f22])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_xboole_0(k1_funct_2(X0,X1)) | v1_xboole_0(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : (~v1_xboole_0(k1_funct_2(X0,X1)) | v1_xboole_0(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (~v1_xboole_0(X1) => ~v1_xboole_0(k1_funct_2(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_funct_2)).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ~v1_xboole_0(sK1) | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    spl3_1 <=> v1_xboole_0(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  % (9967)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (9963)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (9968)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    ~m1_subset_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl3_1 | spl3_2 | ~spl3_4 | ~spl3_5)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f46,f82,f105,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_funct_1(sK2(X0,X1,X2)) | ~m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2(X0,X1,X2),X0,X1) | m1_funct_2(X2,X0,X1) | v1_xboole_0(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ((~m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2(X0,X1,X2),X0,X1) | ~v1_funct_1(sK2(X0,X1,X2))) & m1_subset_1(sK2(X0,X1,X2),X2))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) | ~m1_subset_1(X4,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2)) => ((~m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2(X0,X1,X2),X0,X1) | ~v1_funct_1(sK2(X0,X1,X2))) & m1_subset_1(sK2(X0,X1,X2),X2)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2))) & (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) | ~m1_subset_1(X4,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.21/0.46    inference(rectify,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((m1_funct_2(X2,X0,X1) | ? [X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) & m1_subset_1(X3,X2))) & (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~m1_subset_1(X3,X2)) | ~m1_funct_2(X2,X0,X1))) | v1_xboole_0(X2))),
% 0.21/0.46    inference(nnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_funct_2(X2,X0,X1) <=> ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~m1_subset_1(X3,X2))) | v1_xboole_0(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) => (m1_funct_2(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,X2) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    v1_funct_2(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),sK0,sK1) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f103])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    spl3_5 <=> v1_funct_2(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    v1_funct_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f80])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    spl3_4 <=> v1_funct_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ~m1_funct_2(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)),sK0,sK1) | spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl3_2 <=> m1_funct_2(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)),sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    spl3_5 | spl3_1 | ~spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f84,f57,f39,f103])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    v1_funct_2(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),sK0,sK1) | (spl3_1 | ~spl3_3)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f59,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) | v1_funct_2(X0,X1,X2)) )),
% 0.21/0.46    inference(resolution,[],[f36,f24])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f31,f22])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl3_4 | spl3_1 | ~spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f72,f57,f39,f80])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    v1_funct_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))) | (spl3_1 | ~spl3_3)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f59,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) | v1_funct_1(X0)) )),
% 0.21/0.46    inference(resolution,[],[f37,f24])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | v1_funct_1(X2)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f30,f22])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v1_funct_1(X2) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl3_3 | spl3_1 | spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f51,f44,f39,f57])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    m1_subset_1(sK2(sK0,sK1,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))),k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) | (spl3_1 | spl3_2)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f48,f46,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),X2) | m1_funct_2(X2,X0,X1) | v1_xboole_0(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f33,f44])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ~m1_funct_2(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)),sK0,sK1)),
% 0.21/0.46    inference(definition_unfolding,[],[f21,f22])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ~m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ~m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1) & ~v1_xboole_0(sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0,X1] : (~m1_funct_2(k1_funct_2(X0,X1),X0,X1) & ~v1_xboole_0(X1)) => (~m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1) & ~v1_xboole_0(sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1] : (~m1_funct_2(k1_funct_2(X0,X1),X0,X1) & ~v1_xboole_0(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (~v1_xboole_0(X1) => m1_funct_2(k1_funct_2(X0,X1),X0,X1))),
% 0.21/0.46    inference(negated_conjecture,[],[f6])).
% 0.21/0.46  fof(f6,conjecture,(
% 0.21/0.46    ! [X0,X1] : (~v1_xboole_0(X1) => m1_funct_2(k1_funct_2(X0,X1),X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_funct_2)).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ~spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ~v1_xboole_0(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (9972)------------------------------
% 0.21/0.46  % (9972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (9972)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (9972)Memory used [KB]: 10746
% 0.21/0.46  % (9972)Time elapsed: 0.038 s
% 0.21/0.46  % (9972)------------------------------
% 0.21/0.46  % (9972)------------------------------
% 0.21/0.47  % (9968)Refutation not found, incomplete strategy% (9968)------------------------------
% 0.21/0.47  % (9968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9962)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (9969)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (9958)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (9960)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (9956)Success in time 0.115 s
%------------------------------------------------------------------------------
