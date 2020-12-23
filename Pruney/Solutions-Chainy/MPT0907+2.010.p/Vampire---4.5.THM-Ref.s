%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  75 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  127 ( 191 expanded)
%              Number of equality atoms :   58 (  83 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f51,f61,f73,f85])).

fof(f85,plain,
    ( spl3_4
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f82,f33,f26,f49])).

fof(f49,plain,
    ( spl3_4
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f26,plain,
    ( spl3_1
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f33,plain,
    ( spl3_3
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f82,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f79,f34])).

fof(f34,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_1 ),
    inference(resolution,[],[f78,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( sK0 != sK0
        | ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_1 ),
    inference(superposition,[],[f18,f27])).

fof(f27,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f73,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl3_5 ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f16,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f16,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f60,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_5
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f61,plain,
    ( spl3_5
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f52,f49,f33,f59])).

fof(f52,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f34,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f51,plain,
    ( spl3_4
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f45,f33,f29,f49])).

fof(f29,plain,
    ( spl3_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f17])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f40])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( sK0 != sK0
        | ~ m1_subset_1(sK0,k2_zfmisc_1(X0,X1))
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 )
    | ~ spl3_2 ),
    inference(superposition,[],[f19,f30])).

fof(f30,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).

fof(f31,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f15,f29,f26])).

fof(f15,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (11049)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (11049)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f31,f35,f51,f61,f73,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl3_4 | ~spl3_1 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f82,f33,f26,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl3_4 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    spl3_1 <=> sK0 = k1_mcart_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    spl3_3 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | (~spl3_1 | ~spl3_3)),
% 0.21/0.49    inference(resolution,[],[f79,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f33])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | ~spl3_1),
% 0.21/0.49    inference(resolution,[],[f78,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | ~spl3_1),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sK0 != sK0 | ~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | ~spl3_1),
% 0.21/0.49    inference(superposition,[],[f18,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    sK0 = k1_mcart_1(sK0) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f26])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2) | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k2_zfmisc_1(X0,X1) = k1_xboole_0)),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ~spl3_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    $false | ~spl3_5),
% 0.21/0.49    inference(resolution,[],[f60,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(superposition,[],[f16,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_xboole_0) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_5 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl3_5 | ~spl3_3 | ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f49,f33,f59])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_xboole_0) | (~spl3_3 | ~spl3_4)),
% 0.21/0.49    inference(superposition,[],[f34,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl3_4 | ~spl3_2 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f33,f29,f49])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    spl3_2 <=> sK0 = k2_mcart_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | (~spl3_2 | ~spl3_3)),
% 0.21/0.49    inference(resolution,[],[f42,f34])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | ~spl3_2),
% 0.21/0.49    inference(resolution,[],[f41,f17])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | ~spl3_2),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sK0 != sK0 | ~m1_subset_1(sK0,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) ) | ~spl3_2),
% 0.21/0.49    inference(superposition,[],[f19,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    sK0 = k2_mcart_1(sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f29])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_mcart_1(X2) != X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f14,f33])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    spl3_1 | spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f29,f26])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11049)------------------------------
% 0.21/0.49  % (11049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11049)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11049)Memory used [KB]: 10618
% 0.21/0.49  % (11049)Time elapsed: 0.056 s
% 0.21/0.49  % (11049)------------------------------
% 0.21/0.49  % (11049)------------------------------
% 0.21/0.49  % (11042)Success in time 0.133 s
%------------------------------------------------------------------------------
