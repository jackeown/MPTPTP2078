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
% DateTime   : Thu Dec  3 12:31:17 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  265 ( 533 expanded)
%              Number of leaves         :   65 ( 265 expanded)
%              Depth                    :   11
%              Number of atoms          :  759 (1423 expanded)
%              Number of equality atoms :   62 ( 176 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f67,f72,f76,f82,f87,f92,f102,f106,f134,f143,f149,f170,f182,f201,f208,f212,f222,f229,f251,f256,f289,f306,f319,f341,f351,f356,f380,f641,f662,f763,f974,f978,f1010,f1029,f1060,f1077,f1128,f1489,f2526,f3331,f3553,f4125,f4223,f4545,f4721,f5459,f5471,f5520,f6230,f6242])).

fof(f6242,plain,
    ( spl4_1
    | ~ spl4_306
    | ~ spl4_321 ),
    inference(avatar_contradiction_clause,[],[f6241])).

fof(f6241,plain,
    ( $false
    | spl4_1
    | ~ spl4_306
    | ~ spl4_321 ),
    inference(subsumption_resolution,[],[f6232,f57])).

fof(f57,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f6232,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_306
    | ~ spl4_321 ),
    inference(resolution,[],[f6229,f5519])).

fof(f5519,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2)
        | r1_xboole_0(X2,X3) )
    | ~ spl4_306 ),
    inference(avatar_component_clause,[],[f5518])).

fof(f5518,plain,
    ( spl4_306
  <=> ! [X3,X2] :
        ( r1_xboole_0(X2,X3)
        | ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_306])])).

fof(f6229,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | ~ spl4_321 ),
    inference(avatar_component_clause,[],[f6227])).

fof(f6227,plain,
    ( spl4_321
  <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_321])])).

fof(f6230,plain,
    ( spl4_321
    | ~ spl4_6
    | ~ spl4_303 ),
    inference(avatar_split_clause,[],[f6215,f5469,f79,f6227])).

fof(f79,plain,
    ( spl4_6
  <=> r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f5469,plain,
    ( spl4_303
  <=> ! [X3,X2] :
        ( ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3)
        | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_303])])).

fof(f6215,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | ~ spl4_6
    | ~ spl4_303 ),
    inference(resolution,[],[f5470,f81])).

fof(f81,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f5470,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3)
        | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3) )
    | ~ spl4_303 ),
    inference(avatar_component_clause,[],[f5469])).

fof(f5520,plain,
    ( spl4_306
    | ~ spl4_256
    | ~ spl4_300 ),
    inference(avatar_split_clause,[],[f5481,f5457,f4719,f5518])).

fof(f4719,plain,
    ( spl4_256
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_256])])).

fof(f5457,plain,
    ( spl4_300
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_300])])).

fof(f5481,plain,
    ( ! [X2,X3] :
        ( r1_xboole_0(X2,X3)
        | ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) )
    | ~ spl4_256
    | ~ spl4_300 ),
    inference(resolution,[],[f5458,f4720])).

fof(f4720,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_256 ),
    inference(avatar_component_clause,[],[f4719])).

fof(f5458,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_300 ),
    inference(avatar_component_clause,[],[f5457])).

fof(f5471,plain,
    ( spl4_303
    | ~ spl4_21
    | ~ spl4_224 ),
    inference(avatar_split_clause,[],[f4248,f4221,f168,f5469])).

fof(f168,plain,
    ( spl4_21
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f4221,plain,
    ( spl4_224
  <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_224])])).

fof(f4248,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3)
        | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3) )
    | ~ spl4_21
    | ~ spl4_224 ),
    inference(resolution,[],[f4222,f169])).

fof(f169,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f168])).

fof(f4222,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))
    | ~ spl4_224 ),
    inference(avatar_component_clause,[],[f4221])).

fof(f5459,plain,
    ( spl4_300
    | ~ spl4_77
    | ~ spl4_213 ),
    inference(avatar_split_clause,[],[f4134,f4123,f761,f5457])).

fof(f761,plain,
    ( spl4_77
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f4123,plain,
    ( spl4_213
  <=> ! [X63,X62] :
        ( ~ r2_hidden(X63,X62)
        | ~ r1_xboole_0(X62,X62) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_213])])).

fof(f4134,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_77
    | ~ spl4_213 ),
    inference(resolution,[],[f4124,f762])).

fof(f762,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_77 ),
    inference(avatar_component_clause,[],[f761])).

fof(f4124,plain,
    ( ! [X62,X63] :
        ( ~ r2_hidden(X63,X62)
        | ~ r1_xboole_0(X62,X62) )
    | ~ spl4_213 ),
    inference(avatar_component_clause,[],[f4123])).

fof(f4721,plain,
    ( spl4_256
    | ~ spl4_5
    | ~ spl4_247 ),
    inference(avatar_split_clause,[],[f4554,f4543,f74,f4719])).

fof(f74,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f4543,plain,
    ( spl4_247
  <=> ! [X3,X5,X4] :
        ( ~ r1_xboole_0(X5,X3)
        | r1_xboole_0(X5,k4_xboole_0(X3,k4_xboole_0(X3,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_247])])).

fof(f4554,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) )
    | ~ spl4_5
    | ~ spl4_247 ),
    inference(resolution,[],[f4544,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f4544,plain,
    ( ! [X4,X5,X3] :
        ( r1_xboole_0(X5,k4_xboole_0(X3,k4_xboole_0(X3,X4)))
        | ~ r1_xboole_0(X5,X3) )
    | ~ spl4_247 ),
    inference(avatar_component_clause,[],[f4543])).

fof(f4545,plain,
    ( spl4_247
    | ~ spl4_11
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f204,f199,f104,f4543])).

fof(f104,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f199,plain,
    ( spl4_26
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f204,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_xboole_0(X5,X3)
        | r1_xboole_0(X5,k4_xboole_0(X3,k4_xboole_0(X3,X4))) )
    | ~ spl4_11
    | ~ spl4_26 ),
    inference(superposition,[],[f105,f200])).

fof(f200,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f199])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f4223,plain,
    ( spl4_224
    | ~ spl4_44
    | ~ spl4_161 ),
    inference(avatar_split_clause,[],[f2693,f2524,f349,f4221])).

fof(f349,plain,
    ( spl4_44
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f2524,plain,
    ( spl4_161
  <=> ! [X18] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X18)),k4_xboole_0(sK2,k4_xboole_0(sK2,X18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_161])])).

fof(f2693,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))
    | ~ spl4_44
    | ~ spl4_161 ),
    inference(superposition,[],[f2525,f350])).

fof(f350,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f349])).

fof(f2525,plain,
    ( ! [X18] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X18)),k4_xboole_0(sK2,k4_xboole_0(sK2,X18)))
    | ~ spl4_161 ),
    inference(avatar_component_clause,[],[f2524])).

fof(f4125,plain,
    ( spl4_213
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_23
    | ~ spl4_28
    | ~ spl4_77
    | ~ spl4_91
    | ~ spl4_102
    | ~ spl4_119
    | ~ spl4_205
    | ~ spl4_206 ),
    inference(avatar_split_clause,[],[f3872,f3551,f3329,f1487,f1126,f972,f761,f210,f180,f132,f65,f4123])).

fof(f65,plain,
    ( spl4_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f132,plain,
    ( spl4_16
  <=> ! [X2] : k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f180,plain,
    ( spl4_23
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f210,plain,
    ( spl4_28
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f972,plain,
    ( spl4_91
  <=> ! [X3] :
        ( ~ r1_xboole_0(k1_xboole_0,X3)
        | r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f1126,plain,
    ( spl4_102
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f1487,plain,
    ( spl4_119
  <=> ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).

fof(f3329,plain,
    ( spl4_205
  <=> ! [X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_205])])).

fof(f3551,plain,
    ( spl4_206
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_206])])).

fof(f3872,plain,
    ( ! [X62,X63] :
        ( ~ r2_hidden(X63,X62)
        | ~ r1_xboole_0(X62,X62) )
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_23
    | ~ spl4_28
    | ~ spl4_77
    | ~ spl4_91
    | ~ spl4_102
    | ~ spl4_119
    | ~ spl4_205
    | ~ spl4_206 ),
    inference(forward_demodulation,[],[f3831,f66])).

fof(f66,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f3831,plain,
    ( ! [X62,X63] :
        ( ~ r2_hidden(X63,k4_xboole_0(X62,k1_xboole_0))
        | ~ r1_xboole_0(X62,X62) )
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_23
    | ~ spl4_28
    | ~ spl4_77
    | ~ spl4_91
    | ~ spl4_102
    | ~ spl4_119
    | ~ spl4_205
    | ~ spl4_206 ),
    inference(backward_demodulation,[],[f1927,f3802])).

fof(f3802,plain,
    ( ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5))
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_23
    | ~ spl4_28
    | ~ spl4_77
    | ~ spl4_91
    | ~ spl4_102
    | ~ spl4_119
    | ~ spl4_205
    | ~ spl4_206 ),
    inference(backward_demodulation,[],[f3462,f3579])).

fof(f3579,plain,
    ( ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2
    | ~ spl4_3
    | ~ spl4_16
    | ~ spl4_28
    | ~ spl4_206 ),
    inference(backward_demodulation,[],[f133,f3575])).

fof(f3575,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3)
    | ~ spl4_3
    | ~ spl4_28
    | ~ spl4_206 ),
    inference(forward_demodulation,[],[f3557,f66])).

fof(f3557,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))
    | ~ spl4_28
    | ~ spl4_206 ),
    inference(resolution,[],[f3552,f211])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f210])).

fof(f3552,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_206 ),
    inference(avatar_component_clause,[],[f3551])).

fof(f133,plain,
    ( ! [X2] : k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f3462,plain,
    ( ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X5)))
    | ~ spl4_3
    | ~ spl4_23
    | ~ spl4_28
    | ~ spl4_77
    | ~ spl4_91
    | ~ spl4_102
    | ~ spl4_119
    | ~ spl4_205 ),
    inference(subsumption_resolution,[],[f983,f3449])).

fof(f3449,plain,
    ( ! [X11] : r1_xboole_0(k1_xboole_0,X11)
    | ~ spl4_3
    | ~ spl4_23
    | ~ spl4_77
    | ~ spl4_102
    | ~ spl4_119
    | ~ spl4_205 ),
    inference(subsumption_resolution,[],[f1950,f3447])).

fof(f3447,plain,
    ( ! [X109,X110] : ~ r2_hidden(X110,k4_xboole_0(X109,X109))
    | ~ spl4_3
    | ~ spl4_23
    | ~ spl4_102
    | ~ spl4_205 ),
    inference(forward_demodulation,[],[f3446,f66])).

fof(f3446,plain,
    ( ! [X109,X110] : ~ r2_hidden(X110,k4_xboole_0(k4_xboole_0(X109,X109),k1_xboole_0))
    | ~ spl4_23
    | ~ spl4_102
    | ~ spl4_205 ),
    inference(subsumption_resolution,[],[f3420,f1127])).

fof(f1127,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X1))
    | ~ spl4_102 ),
    inference(avatar_component_clause,[],[f1126])).

fof(f3420,plain,
    ( ! [X109,X110] :
        ( ~ r2_hidden(X110,k4_xboole_0(k4_xboole_0(X109,X109),k1_xboole_0))
        | ~ r1_xboole_0(k4_xboole_0(X109,X109),k4_xboole_0(X109,X109)) )
    | ~ spl4_23
    | ~ spl4_205 ),
    inference(superposition,[],[f181,f3330])).

fof(f3330,plain,
    ( ! [X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X4))
    | ~ spl4_205 ),
    inference(avatar_component_clause,[],[f3329])).

fof(f181,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f180])).

fof(f1950,plain,
    ( ! [X11] :
        ( r2_hidden(sK3(k1_xboole_0,X11),k4_xboole_0(X11,X11))
        | r1_xboole_0(k1_xboole_0,X11) )
    | ~ spl4_77
    | ~ spl4_119 ),
    inference(superposition,[],[f762,f1488])).

fof(f1488,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | ~ spl4_119 ),
    inference(avatar_component_clause,[],[f1487])).

fof(f983,plain,
    ( ! [X5] :
        ( ~ r1_xboole_0(k1_xboole_0,X5)
        | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X5))) )
    | ~ spl4_28
    | ~ spl4_91 ),
    inference(resolution,[],[f973,f211])).

fof(f973,plain,
    ( ! [X3] :
        ( r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X3))
        | ~ r1_xboole_0(k1_xboole_0,X3) )
    | ~ spl4_91 ),
    inference(avatar_component_clause,[],[f972])).

fof(f1927,plain,
    ( ! [X62,X63] :
        ( ~ r2_hidden(X63,k4_xboole_0(X62,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X62))))
        | ~ r1_xboole_0(X62,X62) )
    | ~ spl4_23
    | ~ spl4_119 ),
    inference(superposition,[],[f181,f1488])).

fof(f3553,plain,
    ( spl4_206
    | ~ spl4_3
    | ~ spl4_23
    | ~ spl4_77
    | ~ spl4_102
    | ~ spl4_205 ),
    inference(avatar_split_clause,[],[f3448,f3329,f1126,f761,f180,f65,f3551])).

fof(f3448,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_23
    | ~ spl4_77
    | ~ spl4_102
    | ~ spl4_205 ),
    inference(subsumption_resolution,[],[f893,f3447])).

fof(f893,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,k1_xboole_0),k4_xboole_0(X0,X0))
        | r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl4_3
    | ~ spl4_77 ),
    inference(superposition,[],[f762,f66])).

fof(f3331,plain,
    ( spl4_205
    | ~ spl4_3
    | ~ spl4_28
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f1073,f1058,f210,f65,f3329])).

fof(f1058,plain,
    ( spl4_96
  <=> ! [X0] : r1_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f1073,plain,
    ( ! [X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X4))
    | ~ spl4_3
    | ~ spl4_28
    | ~ spl4_96 ),
    inference(forward_demodulation,[],[f1063,f66])).

fof(f1063,plain,
    ( ! [X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(k4_xboole_0(X4,X4),k1_xboole_0))
    | ~ spl4_28
    | ~ spl4_96 ),
    inference(resolution,[],[f1059,f211])).

fof(f1059,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)
    | ~ spl4_96 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f2526,plain,
    ( spl4_161
    | ~ spl4_2
    | ~ spl4_97 ),
    inference(avatar_split_clause,[],[f1276,f1075,f60,f2524])).

fof(f60,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1075,plain,
    ( spl4_97
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).

fof(f1276,plain,
    ( ! [X18] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X18)),k4_xboole_0(sK2,k4_xboole_0(sK2,X18)))
    | ~ spl4_2
    | ~ spl4_97 ),
    inference(resolution,[],[f1076,f62])).

fof(f62,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f1076,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) )
    | ~ spl4_97 ),
    inference(avatar_component_clause,[],[f1075])).

fof(f1489,plain,
    ( spl4_119
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f617,f349,f65,f1487])).

fof(f617,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | ~ spl4_3
    | ~ spl4_44 ),
    inference(superposition,[],[f350,f66])).

fof(f1128,plain,
    ( spl4_102
    | ~ spl4_92
    | ~ spl4_95 ),
    inference(avatar_split_clause,[],[f1043,f1027,f976,f1126])).

fof(f976,plain,
    ( spl4_92
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | r1_xboole_0(k4_xboole_0(X1,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f1027,plain,
    ( spl4_95
  <=> ! [X5] : r1_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).

fof(f1043,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X1))
    | ~ spl4_92
    | ~ spl4_95 ),
    inference(resolution,[],[f1028,f977])).

fof(f977,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | r1_xboole_0(k4_xboole_0(X1,X1),X0) )
    | ~ spl4_92 ),
    inference(avatar_component_clause,[],[f976])).

fof(f1028,plain,
    ( ! [X5] : r1_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5))
    | ~ spl4_95 ),
    inference(avatar_component_clause,[],[f1027])).

fof(f1077,plain,(
    spl4_97 ),
    inference(avatar_split_clause,[],[f53,f1075])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f34,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f1060,plain,
    ( spl4_96
    | ~ spl4_31
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f993,f976,f226,f1058])).

fof(f226,plain,
    ( spl4_31
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f993,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)
    | ~ spl4_31
    | ~ spl4_92 ),
    inference(resolution,[],[f977,f228])).

fof(f228,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f226])).

fof(f1029,plain,
    ( spl4_95
    | ~ spl4_18
    | ~ spl4_46
    | ~ spl4_93 ),
    inference(avatar_split_clause,[],[f1021,f1008,f377,f147,f1027])).

fof(f147,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k4_xboole_0(X1,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f377,plain,
    ( spl4_46
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f1008,plain,
    ( spl4_93
  <=> ! [X13] : r1_xboole_0(k4_xboole_0(X13,X13),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f1021,plain,
    ( ! [X5] : r1_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5))
    | ~ spl4_18
    | ~ spl4_46
    | ~ spl4_93 ),
    inference(forward_demodulation,[],[f1015,f379])).

fof(f379,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f377])).

fof(f1015,plain,
    ( ! [X5] : r1_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(X5,X5))
    | ~ spl4_18
    | ~ spl4_93 ),
    inference(resolution,[],[f1009,f148])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k4_xboole_0(X1,X1),X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1009,plain,
    ( ! [X13] : r1_xboole_0(k4_xboole_0(X13,X13),sK0)
    | ~ spl4_93 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f1010,plain,
    ( spl4_93
    | ~ spl4_43
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f1005,f976,f338,f1008])).

fof(f338,plain,
    ( spl4_43
  <=> r1_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f1005,plain,
    ( ! [X13] : r1_xboole_0(k4_xboole_0(X13,X13),sK0)
    | ~ spl4_43
    | ~ spl4_92 ),
    inference(resolution,[],[f977,f340])).

fof(f340,plain,
    ( r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f338])).

fof(f978,plain,
    ( spl4_92
    | ~ spl4_21
    | ~ spl4_67 ),
    inference(avatar_split_clause,[],[f663,f660,f168,f976])).

fof(f660,plain,
    ( spl4_67
  <=> ! [X0] : r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f663,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | r1_xboole_0(k4_xboole_0(X1,X1),X0) )
    | ~ spl4_21
    | ~ spl4_67 ),
    inference(resolution,[],[f661,f169])).

fof(f661,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0)
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f660])).

fof(f974,plain,
    ( spl4_91
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f489,f249,f226,f972])).

fof(f249,plain,
    ( spl4_33
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f489,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(k1_xboole_0,X3)
        | r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X3)) )
    | ~ spl4_31
    | ~ spl4_33 ),
    inference(resolution,[],[f250,f228])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r1_xboole_0(X0,X2)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f249])).

fof(f763,plain,(
    spl4_77 ),
    inference(avatar_split_clause,[],[f50,f761])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f662,plain,
    ( spl4_67
    | ~ spl4_3
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f644,f639,f65,f660])).

fof(f639,plain,
    ( spl4_66
  <=> ! [X7,X8] : r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f644,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_66 ),
    inference(superposition,[],[f640,f66])).

fof(f640,plain,
    ( ! [X8,X7] : r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7)
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f639])).

fof(f641,plain,
    ( spl4_66
    | ~ spl4_7
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f622,f349,f85,f639])).

fof(f85,plain,
    ( spl4_7
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f622,plain,
    ( ! [X8,X7] : r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7)
    | ~ spl4_7
    | ~ spl4_44 ),
    inference(superposition,[],[f86,f350])).

fof(f86,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f380,plain,
    ( spl4_46
    | ~ spl4_3
    | ~ spl4_28
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f363,f353,f210,f65,f377])).

fof(f353,plain,
    ( spl4_45
  <=> r1_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f363,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl4_3
    | ~ spl4_28
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f359,f66])).

fof(f359,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl4_28
    | ~ spl4_45 ),
    inference(resolution,[],[f355,f211])).

fof(f355,plain,
    ( r1_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f353])).

fof(f356,plain,
    ( spl4_45
    | ~ spl4_5
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f346,f338,f74,f353])).

fof(f346,plain,
    ( r1_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_43 ),
    inference(resolution,[],[f340,f75])).

fof(f351,plain,(
    spl4_44 ),
    inference(avatar_split_clause,[],[f48,f349])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f34,f34])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f341,plain,
    ( spl4_43
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f334,f316,f210,f147,f69,f65,f338])).

fof(f69,plain,
    ( spl4_4
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f316,plain,
    ( spl4_42
  <=> r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f334,plain,
    ( r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_42 ),
    inference(backward_demodulation,[],[f150,f330])).

fof(f330,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl4_3
    | ~ spl4_28
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f326,f66])).

fof(f326,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0))
    | ~ spl4_28
    | ~ spl4_42 ),
    inference(resolution,[],[f318,f211])).

fof(f318,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f316])).

fof(f150,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl4_4
    | ~ spl4_18 ),
    inference(resolution,[],[f148,f71])).

fof(f71,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f319,plain,
    ( spl4_42
    | ~ spl4_6
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f309,f304,f79,f316])).

fof(f304,plain,
    ( spl4_40
  <=> ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | r1_xboole_0(X1,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f309,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_40 ),
    inference(resolution,[],[f305,f81])).

fof(f305,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | r1_xboole_0(X1,k1_xboole_0) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f304])).

fof(f306,plain,
    ( spl4_40
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f296,f286,f104,f304])).

fof(f286,plain,
    ( spl4_37
  <=> sK0 = k2_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f296,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | r1_xboole_0(X1,k1_xboole_0) )
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(superposition,[],[f105,f288])).

fof(f288,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f286])).

fof(f289,plain,
    ( spl4_37
    | ~ spl4_26
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f259,f253,f199,f286])).

fof(f253,plain,
    ( spl4_34
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f259,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_26
    | ~ spl4_34 ),
    inference(superposition,[],[f200,f255])).

fof(f255,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f253])).

fof(f256,plain,
    ( spl4_34
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f246,f210,f69,f253])).

fof(f246,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(resolution,[],[f211,f71])).

fof(f251,plain,(
    spl4_33 ),
    inference(avatar_split_clause,[],[f41,f249])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f229,plain,
    ( spl4_31
    | ~ spl4_3
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f224,f220,f65,f226])).

fof(f220,plain,
    ( spl4_30
  <=> ! [X0] :
        ( k1_xboole_0 != k4_xboole_0(X0,X0)
        | r1_xboole_0(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f224,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_30 ),
    inference(trivial_inequality_removal,[],[f223])).

fof(f223,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_30 ),
    inference(superposition,[],[f221,f66])).

fof(f221,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k4_xboole_0(X0,X0)
        | r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f220])).

fof(f222,plain,
    ( spl4_30
    | ~ spl4_3
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f218,f206,f65,f220])).

fof(f206,plain,
    ( spl4_27
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f218,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k4_xboole_0(X0,X0)
        | r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl4_3
    | ~ spl4_27 ),
    inference(superposition,[],[f207,f66])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f206])).

fof(f212,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f52,f210])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f208,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f51,f206])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f201,plain,
    ( spl4_26
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f112,f100,f85,f199])).

fof(f100,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f112,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(resolution,[],[f101,f86])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f182,plain,(
    spl4_23 ),
    inference(avatar_split_clause,[],[f49,f180])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f170,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f45,f168])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f149,plain,
    ( spl4_18
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f144,f141,f74,f147])).

fof(f141,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X1,X0)
        | r1_xboole_0(X1,k4_xboole_0(X0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k4_xboole_0(X1,X1),X0) )
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(resolution,[],[f142,f75])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X1,k4_xboole_0(X0,X0))
        | ~ r1_xboole_0(X1,X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl4_17
    | ~ spl4_11
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f136,f132,f104,f141])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,X0)
        | r1_xboole_0(X1,k4_xboole_0(X0,X0)) )
    | ~ spl4_11
    | ~ spl4_16 ),
    inference(superposition,[],[f105,f133])).

fof(f134,plain,
    ( spl4_16
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f113,f100,f90,f132])).

fof(f90,plain,
    ( spl4_8
  <=> ! [X0] : r1_tarski(k4_xboole_0(X0,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f113,plain,
    ( ! [X2] : k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f101,f91])).

fof(f91,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,X0),X0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f106,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f42,f104])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f37,f100])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f92,plain,
    ( spl4_8
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f88,f85,f65,f90])).

fof(f88,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,X0),X0)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(superposition,[],[f86,f66])).

fof(f87,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f82,plain,
    ( spl4_6
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f77,f74,f69,f79])).

fof(f77,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f75,f71])).

fof(f76,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f38,f74])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f72,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f46,f69])).

fof(f46,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f30,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f67,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f63,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (19019)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (19015)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (19016)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (19026)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (19012)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.51  % (19018)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (19029)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (19017)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.51  % (19025)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.51  % (19027)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (19024)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.51  % (19014)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.51  % (19021)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (19023)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.52  % (19013)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.52  % (19020)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.53  % (19022)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.53  % (19028)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.66/0.60  % (19019)Refutation found. Thanks to Tanya!
% 1.66/0.60  % SZS status Theorem for theBenchmark
% 1.66/0.61  % SZS output start Proof for theBenchmark
% 1.66/0.61  fof(f6245,plain,(
% 1.66/0.61    $false),
% 1.66/0.61    inference(avatar_sat_refutation,[],[f58,f63,f67,f72,f76,f82,f87,f92,f102,f106,f134,f143,f149,f170,f182,f201,f208,f212,f222,f229,f251,f256,f289,f306,f319,f341,f351,f356,f380,f641,f662,f763,f974,f978,f1010,f1029,f1060,f1077,f1128,f1489,f2526,f3331,f3553,f4125,f4223,f4545,f4721,f5459,f5471,f5520,f6230,f6242])).
% 1.66/0.61  fof(f6242,plain,(
% 1.66/0.61    spl4_1 | ~spl4_306 | ~spl4_321),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f6241])).
% 1.66/0.61  fof(f6241,plain,(
% 1.66/0.61    $false | (spl4_1 | ~spl4_306 | ~spl4_321)),
% 1.66/0.61    inference(subsumption_resolution,[],[f6232,f57])).
% 1.66/0.61  fof(f57,plain,(
% 1.66/0.61    ~r1_xboole_0(sK0,sK1) | spl4_1),
% 1.66/0.61    inference(avatar_component_clause,[],[f55])).
% 1.66/0.61  fof(f55,plain,(
% 1.66/0.61    spl4_1 <=> r1_xboole_0(sK0,sK1)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.66/0.61  fof(f6232,plain,(
% 1.66/0.61    r1_xboole_0(sK0,sK1) | (~spl4_306 | ~spl4_321)),
% 1.66/0.61    inference(resolution,[],[f6229,f5519])).
% 1.66/0.61  fof(f5519,plain,(
% 1.66/0.61    ( ! [X2,X3] : (~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) | r1_xboole_0(X2,X3)) ) | ~spl4_306),
% 1.66/0.61    inference(avatar_component_clause,[],[f5518])).
% 1.66/0.61  fof(f5518,plain,(
% 1.66/0.61    spl4_306 <=> ! [X3,X2] : (r1_xboole_0(X2,X3) | ~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_306])])).
% 1.66/0.61  fof(f6229,plain,(
% 1.66/0.61    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | ~spl4_321),
% 1.66/0.61    inference(avatar_component_clause,[],[f6227])).
% 1.66/0.61  fof(f6227,plain,(
% 1.66/0.61    spl4_321 <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_321])])).
% 1.66/0.61  fof(f6230,plain,(
% 1.66/0.61    spl4_321 | ~spl4_6 | ~spl4_303),
% 1.66/0.61    inference(avatar_split_clause,[],[f6215,f5469,f79,f6227])).
% 1.66/0.61  fof(f79,plain,(
% 1.66/0.61    spl4_6 <=> r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.66/0.61  fof(f5469,plain,(
% 1.66/0.61    spl4_303 <=> ! [X3,X2] : (~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3) | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_303])])).
% 1.66/0.61  fof(f6215,plain,(
% 1.66/0.61    r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | (~spl4_6 | ~spl4_303)),
% 1.66/0.61    inference(resolution,[],[f5470,f81])).
% 1.66/0.61  fof(f81,plain,(
% 1.66/0.61    r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) | ~spl4_6),
% 1.66/0.61    inference(avatar_component_clause,[],[f79])).
% 1.66/0.61  fof(f5470,plain,(
% 1.66/0.61    ( ! [X2,X3] : (~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3) | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3)) ) | ~spl4_303),
% 1.66/0.61    inference(avatar_component_clause,[],[f5469])).
% 1.66/0.61  fof(f5520,plain,(
% 1.66/0.61    spl4_306 | ~spl4_256 | ~spl4_300),
% 1.66/0.61    inference(avatar_split_clause,[],[f5481,f5457,f4719,f5518])).
% 1.66/0.61  fof(f4719,plain,(
% 1.66/0.61    spl4_256 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_256])])).
% 1.66/0.61  fof(f5457,plain,(
% 1.66/0.61    spl4_300 <=> ! [X1,X0] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_300])])).
% 1.66/0.61  fof(f5481,plain,(
% 1.66/0.61    ( ! [X2,X3] : (r1_xboole_0(X2,X3) | ~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2)) ) | (~spl4_256 | ~spl4_300)),
% 1.66/0.61    inference(resolution,[],[f5458,f4720])).
% 1.66/0.61  fof(f4720,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) | ~r1_xboole_0(X0,X1)) ) | ~spl4_256),
% 1.66/0.61    inference(avatar_component_clause,[],[f4719])).
% 1.66/0.61  fof(f5458,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) ) | ~spl4_300),
% 1.66/0.61    inference(avatar_component_clause,[],[f5457])).
% 1.66/0.61  fof(f5471,plain,(
% 1.66/0.61    spl4_303 | ~spl4_21 | ~spl4_224),
% 1.66/0.61    inference(avatar_split_clause,[],[f4248,f4221,f168,f5469])).
% 1.66/0.61  fof(f168,plain,(
% 1.66/0.61    spl4_21 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.66/0.61  fof(f4221,plain,(
% 1.66/0.61    spl4_224 <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_224])])).
% 1.66/0.61  fof(f4248,plain,(
% 1.66/0.61    ( ! [X2,X3] : (~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sK2)),X3) | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X2)),X3)) ) | (~spl4_21 | ~spl4_224)),
% 1.66/0.61    inference(resolution,[],[f4222,f169])).
% 1.66/0.61  fof(f169,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl4_21),
% 1.66/0.61    inference(avatar_component_clause,[],[f168])).
% 1.66/0.61  fof(f4222,plain,(
% 1.66/0.61    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) ) | ~spl4_224),
% 1.66/0.61    inference(avatar_component_clause,[],[f4221])).
% 1.66/0.61  fof(f5459,plain,(
% 1.66/0.61    spl4_300 | ~spl4_77 | ~spl4_213),
% 1.66/0.61    inference(avatar_split_clause,[],[f4134,f4123,f761,f5457])).
% 1.66/0.61  fof(f761,plain,(
% 1.66/0.61    spl4_77 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 1.66/0.61  fof(f4123,plain,(
% 1.66/0.61    spl4_213 <=> ! [X63,X62] : (~r2_hidden(X63,X62) | ~r1_xboole_0(X62,X62))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_213])])).
% 1.66/0.61  fof(f4134,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) ) | (~spl4_77 | ~spl4_213)),
% 1.66/0.61    inference(resolution,[],[f4124,f762])).
% 1.66/0.61  fof(f762,plain,(
% 1.66/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) ) | ~spl4_77),
% 1.66/0.61    inference(avatar_component_clause,[],[f761])).
% 1.66/0.61  fof(f4124,plain,(
% 1.66/0.61    ( ! [X62,X63] : (~r2_hidden(X63,X62) | ~r1_xboole_0(X62,X62)) ) | ~spl4_213),
% 1.66/0.61    inference(avatar_component_clause,[],[f4123])).
% 1.66/0.61  fof(f4721,plain,(
% 1.66/0.61    spl4_256 | ~spl4_5 | ~spl4_247),
% 1.66/0.61    inference(avatar_split_clause,[],[f4554,f4543,f74,f4719])).
% 1.66/0.61  fof(f74,plain,(
% 1.66/0.61    spl4_5 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.66/0.61  fof(f4543,plain,(
% 1.66/0.61    spl4_247 <=> ! [X3,X5,X4] : (~r1_xboole_0(X5,X3) | r1_xboole_0(X5,k4_xboole_0(X3,k4_xboole_0(X3,X4))))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_247])])).
% 1.66/0.61  fof(f4554,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0)) ) | (~spl4_5 | ~spl4_247)),
% 1.66/0.61    inference(resolution,[],[f4544,f75])).
% 1.66/0.61  fof(f75,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_5),
% 1.66/0.61    inference(avatar_component_clause,[],[f74])).
% 1.66/0.61  fof(f4544,plain,(
% 1.66/0.61    ( ! [X4,X5,X3] : (r1_xboole_0(X5,k4_xboole_0(X3,k4_xboole_0(X3,X4))) | ~r1_xboole_0(X5,X3)) ) | ~spl4_247),
% 1.66/0.61    inference(avatar_component_clause,[],[f4543])).
% 1.66/0.61  fof(f4545,plain,(
% 1.66/0.61    spl4_247 | ~spl4_11 | ~spl4_26),
% 1.66/0.61    inference(avatar_split_clause,[],[f204,f199,f104,f4543])).
% 1.66/0.61  fof(f104,plain,(
% 1.66/0.61    spl4_11 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.66/0.61  fof(f199,plain,(
% 1.66/0.61    spl4_26 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.66/0.61  fof(f204,plain,(
% 1.66/0.61    ( ! [X4,X5,X3] : (~r1_xboole_0(X5,X3) | r1_xboole_0(X5,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) ) | (~spl4_11 | ~spl4_26)),
% 1.66/0.61    inference(superposition,[],[f105,f200])).
% 1.66/0.61  fof(f200,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0) ) | ~spl4_26),
% 1.66/0.61    inference(avatar_component_clause,[],[f199])).
% 1.66/0.61  fof(f105,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) ) | ~spl4_11),
% 1.66/0.61    inference(avatar_component_clause,[],[f104])).
% 1.66/0.61  fof(f4223,plain,(
% 1.66/0.61    spl4_224 | ~spl4_44 | ~spl4_161),
% 1.66/0.61    inference(avatar_split_clause,[],[f2693,f2524,f349,f4221])).
% 1.66/0.61  fof(f349,plain,(
% 1.66/0.61    spl4_44 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.66/0.61  fof(f2524,plain,(
% 1.66/0.61    spl4_161 <=> ! [X18] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X18)),k4_xboole_0(sK2,k4_xboole_0(sK2,X18)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_161])])).
% 1.66/0.61  fof(f2693,plain,(
% 1.66/0.61    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) ) | (~spl4_44 | ~spl4_161)),
% 1.66/0.61    inference(superposition,[],[f2525,f350])).
% 1.66/0.61  fof(f350,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl4_44),
% 1.66/0.61    inference(avatar_component_clause,[],[f349])).
% 1.66/0.61  fof(f2525,plain,(
% 1.66/0.61    ( ! [X18] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X18)),k4_xboole_0(sK2,k4_xboole_0(sK2,X18)))) ) | ~spl4_161),
% 1.66/0.61    inference(avatar_component_clause,[],[f2524])).
% 1.66/0.61  fof(f4125,plain,(
% 1.66/0.61    spl4_213 | ~spl4_3 | ~spl4_16 | ~spl4_23 | ~spl4_28 | ~spl4_77 | ~spl4_91 | ~spl4_102 | ~spl4_119 | ~spl4_205 | ~spl4_206),
% 1.66/0.61    inference(avatar_split_clause,[],[f3872,f3551,f3329,f1487,f1126,f972,f761,f210,f180,f132,f65,f4123])).
% 1.66/0.61  fof(f65,plain,(
% 1.66/0.61    spl4_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.66/0.61  fof(f132,plain,(
% 1.66/0.61    spl4_16 <=> ! [X2] : k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.66/0.61  fof(f180,plain,(
% 1.66/0.61    spl4_23 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.66/0.61  fof(f210,plain,(
% 1.66/0.61    spl4_28 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.66/0.61  fof(f972,plain,(
% 1.66/0.61    spl4_91 <=> ! [X3] : (~r1_xboole_0(k1_xboole_0,X3) | r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X3)))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).
% 1.66/0.61  fof(f1126,plain,(
% 1.66/0.61    spl4_102 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X1))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).
% 1.66/0.61  fof(f1487,plain,(
% 1.66/0.61    spl4_119 <=> ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).
% 1.66/0.61  fof(f3329,plain,(
% 1.66/0.61    spl4_205 <=> ! [X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X4))),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_205])])).
% 1.66/0.61  fof(f3551,plain,(
% 1.66/0.61    spl4_206 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_206])])).
% 1.66/0.61  fof(f3872,plain,(
% 1.66/0.61    ( ! [X62,X63] : (~r2_hidden(X63,X62) | ~r1_xboole_0(X62,X62)) ) | (~spl4_3 | ~spl4_16 | ~spl4_23 | ~spl4_28 | ~spl4_77 | ~spl4_91 | ~spl4_102 | ~spl4_119 | ~spl4_205 | ~spl4_206)),
% 1.66/0.61    inference(forward_demodulation,[],[f3831,f66])).
% 1.66/0.61  fof(f66,plain,(
% 1.66/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_3),
% 1.66/0.61    inference(avatar_component_clause,[],[f65])).
% 1.66/0.61  fof(f3831,plain,(
% 1.66/0.61    ( ! [X62,X63] : (~r2_hidden(X63,k4_xboole_0(X62,k1_xboole_0)) | ~r1_xboole_0(X62,X62)) ) | (~spl4_3 | ~spl4_16 | ~spl4_23 | ~spl4_28 | ~spl4_77 | ~spl4_91 | ~spl4_102 | ~spl4_119 | ~spl4_205 | ~spl4_206)),
% 1.66/0.61    inference(backward_demodulation,[],[f1927,f3802])).
% 1.66/0.61  fof(f3802,plain,(
% 1.66/0.61    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5))) ) | (~spl4_3 | ~spl4_16 | ~spl4_23 | ~spl4_28 | ~spl4_77 | ~spl4_91 | ~spl4_102 | ~spl4_119 | ~spl4_205 | ~spl4_206)),
% 1.66/0.61    inference(backward_demodulation,[],[f3462,f3579])).
% 1.66/0.62  fof(f3579,plain,(
% 1.66/0.62    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) ) | (~spl4_3 | ~spl4_16 | ~spl4_28 | ~spl4_206)),
% 1.66/0.62    inference(backward_demodulation,[],[f133,f3575])).
% 1.66/0.62  fof(f3575,plain,(
% 1.66/0.62    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) ) | (~spl4_3 | ~spl4_28 | ~spl4_206)),
% 1.66/0.62    inference(forward_demodulation,[],[f3557,f66])).
% 1.66/0.62  fof(f3557,plain,(
% 1.66/0.62    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) ) | (~spl4_28 | ~spl4_206)),
% 1.66/0.62    inference(resolution,[],[f3552,f211])).
% 1.66/0.62  fof(f211,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl4_28),
% 1.66/0.62    inference(avatar_component_clause,[],[f210])).
% 1.66/0.62  fof(f3552,plain,(
% 1.66/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl4_206),
% 1.66/0.62    inference(avatar_component_clause,[],[f3551])).
% 1.66/0.62  fof(f133,plain,(
% 1.66/0.62    ( ! [X2] : (k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2) ) | ~spl4_16),
% 1.66/0.62    inference(avatar_component_clause,[],[f132])).
% 1.66/0.62  fof(f3462,plain,(
% 1.66/0.62    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X5)))) ) | (~spl4_3 | ~spl4_23 | ~spl4_28 | ~spl4_77 | ~spl4_91 | ~spl4_102 | ~spl4_119 | ~spl4_205)),
% 1.66/0.62    inference(subsumption_resolution,[],[f983,f3449])).
% 1.66/0.62  fof(f3449,plain,(
% 1.66/0.62    ( ! [X11] : (r1_xboole_0(k1_xboole_0,X11)) ) | (~spl4_3 | ~spl4_23 | ~spl4_77 | ~spl4_102 | ~spl4_119 | ~spl4_205)),
% 1.66/0.62    inference(subsumption_resolution,[],[f1950,f3447])).
% 1.66/0.62  fof(f3447,plain,(
% 1.66/0.62    ( ! [X109,X110] : (~r2_hidden(X110,k4_xboole_0(X109,X109))) ) | (~spl4_3 | ~spl4_23 | ~spl4_102 | ~spl4_205)),
% 1.66/0.62    inference(forward_demodulation,[],[f3446,f66])).
% 1.66/0.62  fof(f3446,plain,(
% 1.66/0.62    ( ! [X109,X110] : (~r2_hidden(X110,k4_xboole_0(k4_xboole_0(X109,X109),k1_xboole_0))) ) | (~spl4_23 | ~spl4_102 | ~spl4_205)),
% 1.66/0.62    inference(subsumption_resolution,[],[f3420,f1127])).
% 1.66/0.62  fof(f1127,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X1))) ) | ~spl4_102),
% 1.66/0.62    inference(avatar_component_clause,[],[f1126])).
% 1.66/0.62  fof(f3420,plain,(
% 1.66/0.62    ( ! [X109,X110] : (~r2_hidden(X110,k4_xboole_0(k4_xboole_0(X109,X109),k1_xboole_0)) | ~r1_xboole_0(k4_xboole_0(X109,X109),k4_xboole_0(X109,X109))) ) | (~spl4_23 | ~spl4_205)),
% 1.66/0.62    inference(superposition,[],[f181,f3330])).
% 1.66/0.62  fof(f3330,plain,(
% 1.66/0.62    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X4))) ) | ~spl4_205),
% 1.66/0.62    inference(avatar_component_clause,[],[f3329])).
% 1.66/0.62  fof(f181,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) ) | ~spl4_23),
% 1.66/0.62    inference(avatar_component_clause,[],[f180])).
% 1.66/0.62  fof(f1950,plain,(
% 1.66/0.62    ( ! [X11] : (r2_hidden(sK3(k1_xboole_0,X11),k4_xboole_0(X11,X11)) | r1_xboole_0(k1_xboole_0,X11)) ) | (~spl4_77 | ~spl4_119)),
% 1.66/0.62    inference(superposition,[],[f762,f1488])).
% 1.66/0.62  fof(f1488,plain,(
% 1.66/0.62    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ) | ~spl4_119),
% 1.66/0.62    inference(avatar_component_clause,[],[f1487])).
% 1.66/0.62  fof(f983,plain,(
% 1.66/0.62    ( ! [X5] : (~r1_xboole_0(k1_xboole_0,X5) | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X5)))) ) | (~spl4_28 | ~spl4_91)),
% 1.66/0.62    inference(resolution,[],[f973,f211])).
% 1.66/0.62  fof(f973,plain,(
% 1.66/0.62    ( ! [X3] : (r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X3)) | ~r1_xboole_0(k1_xboole_0,X3)) ) | ~spl4_91),
% 1.66/0.62    inference(avatar_component_clause,[],[f972])).
% 1.66/0.62  fof(f1927,plain,(
% 1.66/0.62    ( ! [X62,X63] : (~r2_hidden(X63,k4_xboole_0(X62,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X62)))) | ~r1_xboole_0(X62,X62)) ) | (~spl4_23 | ~spl4_119)),
% 1.66/0.62    inference(superposition,[],[f181,f1488])).
% 1.66/0.62  fof(f3553,plain,(
% 1.66/0.62    spl4_206 | ~spl4_3 | ~spl4_23 | ~spl4_77 | ~spl4_102 | ~spl4_205),
% 1.66/0.62    inference(avatar_split_clause,[],[f3448,f3329,f1126,f761,f180,f65,f3551])).
% 1.66/0.62  fof(f3448,plain,(
% 1.66/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl4_3 | ~spl4_23 | ~spl4_77 | ~spl4_102 | ~spl4_205)),
% 1.66/0.62    inference(subsumption_resolution,[],[f893,f3447])).
% 1.66/0.62  fof(f893,plain,(
% 1.66/0.62    ( ! [X0] : (r2_hidden(sK3(X0,k1_xboole_0),k4_xboole_0(X0,X0)) | r1_xboole_0(X0,k1_xboole_0)) ) | (~spl4_3 | ~spl4_77)),
% 1.66/0.62    inference(superposition,[],[f762,f66])).
% 1.66/0.62  fof(f3331,plain,(
% 1.66/0.62    spl4_205 | ~spl4_3 | ~spl4_28 | ~spl4_96),
% 1.66/0.62    inference(avatar_split_clause,[],[f1073,f1058,f210,f65,f3329])).
% 1.66/0.62  fof(f1058,plain,(
% 1.66/0.62    spl4_96 <=> ! [X0] : r1_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).
% 1.66/0.62  fof(f1073,plain,(
% 1.66/0.62    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(X4,X4))) ) | (~spl4_3 | ~spl4_28 | ~spl4_96)),
% 1.66/0.62    inference(forward_demodulation,[],[f1063,f66])).
% 1.66/0.62  fof(f1063,plain,(
% 1.66/0.62    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X4),k4_xboole_0(k4_xboole_0(X4,X4),k1_xboole_0))) ) | (~spl4_28 | ~spl4_96)),
% 1.66/0.62    inference(resolution,[],[f1059,f211])).
% 1.66/0.62  fof(f1059,plain,(
% 1.66/0.62    ( ! [X0] : (r1_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)) ) | ~spl4_96),
% 1.66/0.62    inference(avatar_component_clause,[],[f1058])).
% 1.66/0.62  fof(f2526,plain,(
% 1.66/0.62    spl4_161 | ~spl4_2 | ~spl4_97),
% 1.66/0.62    inference(avatar_split_clause,[],[f1276,f1075,f60,f2524])).
% 1.66/0.62  fof(f60,plain,(
% 1.66/0.62    spl4_2 <=> r1_tarski(sK0,sK2)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.66/0.62  fof(f1075,plain,(
% 1.66/0.62    spl4_97 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).
% 1.66/0.62  fof(f1276,plain,(
% 1.66/0.62    ( ! [X18] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,X18)),k4_xboole_0(sK2,k4_xboole_0(sK2,X18)))) ) | (~spl4_2 | ~spl4_97)),
% 1.66/0.62    inference(resolution,[],[f1076,f62])).
% 1.66/0.62  fof(f62,plain,(
% 1.66/0.62    r1_tarski(sK0,sK2) | ~spl4_2),
% 1.66/0.62    inference(avatar_component_clause,[],[f60])).
% 1.66/0.62  fof(f1076,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ) | ~spl4_97),
% 1.66/0.62    inference(avatar_component_clause,[],[f1075])).
% 1.66/0.62  fof(f1489,plain,(
% 1.66/0.62    spl4_119 | ~spl4_3 | ~spl4_44),
% 1.66/0.62    inference(avatar_split_clause,[],[f617,f349,f65,f1487])).
% 1.66/0.62  fof(f617,plain,(
% 1.66/0.62    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ) | (~spl4_3 | ~spl4_44)),
% 1.66/0.62    inference(superposition,[],[f350,f66])).
% 1.66/0.62  fof(f1128,plain,(
% 1.66/0.62    spl4_102 | ~spl4_92 | ~spl4_95),
% 1.66/0.62    inference(avatar_split_clause,[],[f1043,f1027,f976,f1126])).
% 1.66/0.62  fof(f976,plain,(
% 1.66/0.62    spl4_92 <=> ! [X1,X0] : (~r1_xboole_0(k1_xboole_0,X0) | r1_xboole_0(k4_xboole_0(X1,X1),X0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).
% 1.66/0.62  fof(f1027,plain,(
% 1.66/0.62    spl4_95 <=> ! [X5] : r1_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).
% 1.66/0.62  fof(f1043,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X1))) ) | (~spl4_92 | ~spl4_95)),
% 1.66/0.62    inference(resolution,[],[f1028,f977])).
% 1.66/0.62  fof(f977,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_xboole_0(k1_xboole_0,X0) | r1_xboole_0(k4_xboole_0(X1,X1),X0)) ) | ~spl4_92),
% 1.66/0.62    inference(avatar_component_clause,[],[f976])).
% 1.66/0.62  fof(f1028,plain,(
% 1.66/0.62    ( ! [X5] : (r1_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5))) ) | ~spl4_95),
% 1.66/0.62    inference(avatar_component_clause,[],[f1027])).
% 1.66/0.62  fof(f1077,plain,(
% 1.66/0.62    spl4_97),
% 1.66/0.62    inference(avatar_split_clause,[],[f53,f1075])).
% 1.66/0.62  fof(f53,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 1.66/0.62    inference(definition_unfolding,[],[f44,f34,f34])).
% 1.66/0.62  fof(f34,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f9])).
% 1.66/0.62  fof(f9,axiom,(
% 1.66/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.66/0.62  fof(f44,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f20])).
% 1.66/0.62  fof(f20,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f7])).
% 1.66/0.62  fof(f7,axiom,(
% 1.66/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).
% 1.66/0.62  fof(f1060,plain,(
% 1.66/0.62    spl4_96 | ~spl4_31 | ~spl4_92),
% 1.66/0.62    inference(avatar_split_clause,[],[f993,f976,f226,f1058])).
% 1.66/0.62  fof(f226,plain,(
% 1.66/0.62    spl4_31 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.66/0.62  fof(f993,plain,(
% 1.66/0.62    ( ! [X0] : (r1_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)) ) | (~spl4_31 | ~spl4_92)),
% 1.66/0.62    inference(resolution,[],[f977,f228])).
% 1.66/0.62  fof(f228,plain,(
% 1.66/0.62    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_31),
% 1.66/0.62    inference(avatar_component_clause,[],[f226])).
% 1.66/0.62  fof(f1029,plain,(
% 1.66/0.62    spl4_95 | ~spl4_18 | ~spl4_46 | ~spl4_93),
% 1.66/0.62    inference(avatar_split_clause,[],[f1021,f1008,f377,f147,f1027])).
% 1.66/0.62  fof(f147,plain,(
% 1.66/0.62    spl4_18 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X1,X1),X0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.66/0.62  fof(f377,plain,(
% 1.66/0.62    spl4_46 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.66/0.62  fof(f1008,plain,(
% 1.66/0.62    spl4_93 <=> ! [X13] : r1_xboole_0(k4_xboole_0(X13,X13),sK0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 1.66/0.62  fof(f1021,plain,(
% 1.66/0.62    ( ! [X5] : (r1_xboole_0(k1_xboole_0,k4_xboole_0(X5,X5))) ) | (~spl4_18 | ~spl4_46 | ~spl4_93)),
% 1.66/0.62    inference(forward_demodulation,[],[f1015,f379])).
% 1.66/0.62  fof(f379,plain,(
% 1.66/0.62    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl4_46),
% 1.66/0.62    inference(avatar_component_clause,[],[f377])).
% 1.66/0.62  fof(f1015,plain,(
% 1.66/0.62    ( ! [X5] : (r1_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(X5,X5))) ) | (~spl4_18 | ~spl4_93)),
% 1.66/0.62    inference(resolution,[],[f1009,f148])).
% 1.66/0.62  fof(f148,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X1,X1),X0)) ) | ~spl4_18),
% 1.66/0.62    inference(avatar_component_clause,[],[f147])).
% 1.66/0.62  fof(f1009,plain,(
% 1.66/0.62    ( ! [X13] : (r1_xboole_0(k4_xboole_0(X13,X13),sK0)) ) | ~spl4_93),
% 1.66/0.62    inference(avatar_component_clause,[],[f1008])).
% 1.66/0.62  fof(f1010,plain,(
% 1.66/0.62    spl4_93 | ~spl4_43 | ~spl4_92),
% 1.66/0.62    inference(avatar_split_clause,[],[f1005,f976,f338,f1008])).
% 1.66/0.62  fof(f338,plain,(
% 1.66/0.62    spl4_43 <=> r1_xboole_0(k1_xboole_0,sK0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.66/0.62  fof(f1005,plain,(
% 1.66/0.62    ( ! [X13] : (r1_xboole_0(k4_xboole_0(X13,X13),sK0)) ) | (~spl4_43 | ~spl4_92)),
% 1.66/0.62    inference(resolution,[],[f977,f340])).
% 1.66/0.62  fof(f340,plain,(
% 1.66/0.62    r1_xboole_0(k1_xboole_0,sK0) | ~spl4_43),
% 1.66/0.62    inference(avatar_component_clause,[],[f338])).
% 1.66/0.62  fof(f978,plain,(
% 1.66/0.62    spl4_92 | ~spl4_21 | ~spl4_67),
% 1.66/0.62    inference(avatar_split_clause,[],[f663,f660,f168,f976])).
% 1.66/0.62  fof(f660,plain,(
% 1.66/0.62    spl4_67 <=> ! [X0] : r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.66/0.62  fof(f663,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_xboole_0(k1_xboole_0,X0) | r1_xboole_0(k4_xboole_0(X1,X1),X0)) ) | (~spl4_21 | ~spl4_67)),
% 1.66/0.62    inference(resolution,[],[f661,f169])).
% 1.66/0.62  fof(f661,plain,(
% 1.66/0.62    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0)) ) | ~spl4_67),
% 1.66/0.62    inference(avatar_component_clause,[],[f660])).
% 1.66/0.62  fof(f974,plain,(
% 1.66/0.62    spl4_91 | ~spl4_31 | ~spl4_33),
% 1.66/0.62    inference(avatar_split_clause,[],[f489,f249,f226,f972])).
% 1.66/0.62  fof(f249,plain,(
% 1.66/0.62    spl4_33 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.66/0.62  fof(f489,plain,(
% 1.66/0.62    ( ! [X3] : (~r1_xboole_0(k1_xboole_0,X3) | r1_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X3))) ) | (~spl4_31 | ~spl4_33)),
% 1.66/0.62    inference(resolution,[],[f250,f228])).
% 1.66/0.62  fof(f250,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl4_33),
% 1.66/0.62    inference(avatar_component_clause,[],[f249])).
% 1.66/0.62  fof(f763,plain,(
% 1.66/0.62    spl4_77),
% 1.66/0.62    inference(avatar_split_clause,[],[f50,f761])).
% 1.66/0.62  fof(f50,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.66/0.62    inference(definition_unfolding,[],[f35,f34])).
% 1.66/0.62  fof(f35,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f26])).
% 1.66/0.62  fof(f26,plain,(
% 1.66/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.66/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f25])).
% 1.66/0.62  fof(f25,plain,(
% 1.66/0.62    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.66/0.62    introduced(choice_axiom,[])).
% 1.66/0.62  fof(f16,plain,(
% 1.66/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.66/0.62    inference(ennf_transformation,[],[f14])).
% 1.66/0.62  fof(f14,plain,(
% 1.66/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.66/0.62    inference(rectify,[],[f4])).
% 1.66/0.62  fof(f4,axiom,(
% 1.66/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.66/0.62  fof(f662,plain,(
% 1.66/0.62    spl4_67 | ~spl4_3 | ~spl4_66),
% 1.66/0.62    inference(avatar_split_clause,[],[f644,f639,f65,f660])).
% 1.66/0.62  fof(f639,plain,(
% 1.66/0.62    spl4_66 <=> ! [X7,X8] : r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 1.66/0.62  fof(f644,plain,(
% 1.66/0.62    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0)) ) | (~spl4_3 | ~spl4_66)),
% 1.66/0.62    inference(superposition,[],[f640,f66])).
% 1.66/0.62  fof(f640,plain,(
% 1.66/0.62    ( ! [X8,X7] : (r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7)) ) | ~spl4_66),
% 1.66/0.62    inference(avatar_component_clause,[],[f639])).
% 1.66/0.62  fof(f641,plain,(
% 1.66/0.62    spl4_66 | ~spl4_7 | ~spl4_44),
% 1.66/0.62    inference(avatar_split_clause,[],[f622,f349,f85,f639])).
% 1.66/0.62  fof(f85,plain,(
% 1.66/0.62    spl4_7 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.66/0.62  fof(f622,plain,(
% 1.66/0.62    ( ! [X8,X7] : (r1_tarski(k4_xboole_0(X8,k4_xboole_0(X8,X7)),X7)) ) | (~spl4_7 | ~spl4_44)),
% 1.66/0.62    inference(superposition,[],[f86,f350])).
% 1.66/0.62  fof(f86,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ) | ~spl4_7),
% 1.66/0.62    inference(avatar_component_clause,[],[f85])).
% 1.66/0.62  fof(f380,plain,(
% 1.66/0.62    spl4_46 | ~spl4_3 | ~spl4_28 | ~spl4_45),
% 1.66/0.62    inference(avatar_split_clause,[],[f363,f353,f210,f65,f377])).
% 1.66/0.62  fof(f353,plain,(
% 1.66/0.62    spl4_45 <=> r1_xboole_0(sK0,k1_xboole_0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.66/0.62  fof(f363,plain,(
% 1.66/0.62    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl4_3 | ~spl4_28 | ~spl4_45)),
% 1.66/0.62    inference(forward_demodulation,[],[f359,f66])).
% 1.66/0.62  fof(f359,plain,(
% 1.66/0.62    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) | (~spl4_28 | ~spl4_45)),
% 1.66/0.62    inference(resolution,[],[f355,f211])).
% 1.66/0.62  fof(f355,plain,(
% 1.66/0.62    r1_xboole_0(sK0,k1_xboole_0) | ~spl4_45),
% 1.66/0.62    inference(avatar_component_clause,[],[f353])).
% 1.66/0.62  fof(f356,plain,(
% 1.66/0.62    spl4_45 | ~spl4_5 | ~spl4_43),
% 1.66/0.62    inference(avatar_split_clause,[],[f346,f338,f74,f353])).
% 1.66/0.62  fof(f346,plain,(
% 1.66/0.62    r1_xboole_0(sK0,k1_xboole_0) | (~spl4_5 | ~spl4_43)),
% 1.66/0.62    inference(resolution,[],[f340,f75])).
% 1.66/0.62  fof(f351,plain,(
% 1.66/0.62    spl4_44),
% 1.66/0.62    inference(avatar_split_clause,[],[f48,f349])).
% 1.66/0.62  fof(f48,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.66/0.62    inference(definition_unfolding,[],[f33,f34,f34])).
% 1.66/0.62  fof(f33,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f1])).
% 1.66/0.62  fof(f1,axiom,(
% 1.66/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.66/0.62  fof(f341,plain,(
% 1.66/0.62    spl4_43 | ~spl4_3 | ~spl4_4 | ~spl4_18 | ~spl4_28 | ~spl4_42),
% 1.66/0.62    inference(avatar_split_clause,[],[f334,f316,f210,f147,f69,f65,f338])).
% 1.66/0.62  fof(f69,plain,(
% 1.66/0.62    spl4_4 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.66/0.62  fof(f316,plain,(
% 1.66/0.62    spl4_42 <=> r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.66/0.62  fof(f334,plain,(
% 1.66/0.62    r1_xboole_0(k1_xboole_0,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_18 | ~spl4_28 | ~spl4_42)),
% 1.66/0.62    inference(backward_demodulation,[],[f150,f330])).
% 1.66/0.62  fof(f330,plain,(
% 1.66/0.62    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | (~spl4_3 | ~spl4_28 | ~spl4_42)),
% 1.66/0.62    inference(forward_demodulation,[],[f326,f66])).
% 1.66/0.62  fof(f326,plain,(
% 1.66/0.62    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)) | (~spl4_28 | ~spl4_42)),
% 1.66/0.62    inference(resolution,[],[f318,f211])).
% 1.66/0.62  fof(f318,plain,(
% 1.66/0.62    r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) | ~spl4_42),
% 1.66/0.62    inference(avatar_component_clause,[],[f316])).
% 1.66/0.62  fof(f150,plain,(
% 1.66/0.62    r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),sK0) | (~spl4_4 | ~spl4_18)),
% 1.66/0.62    inference(resolution,[],[f148,f71])).
% 1.66/0.62  fof(f71,plain,(
% 1.66/0.62    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl4_4),
% 1.66/0.62    inference(avatar_component_clause,[],[f69])).
% 1.66/0.62  fof(f319,plain,(
% 1.66/0.62    spl4_42 | ~spl4_6 | ~spl4_40),
% 1.66/0.62    inference(avatar_split_clause,[],[f309,f304,f79,f316])).
% 1.66/0.62  fof(f304,plain,(
% 1.66/0.62    spl4_40 <=> ! [X1] : (~r1_xboole_0(X1,sK0) | r1_xboole_0(X1,k1_xboole_0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.66/0.62  fof(f309,plain,(
% 1.66/0.62    r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) | (~spl4_6 | ~spl4_40)),
% 1.66/0.62    inference(resolution,[],[f305,f81])).
% 1.66/0.62  fof(f305,plain,(
% 1.66/0.62    ( ! [X1] : (~r1_xboole_0(X1,sK0) | r1_xboole_0(X1,k1_xboole_0)) ) | ~spl4_40),
% 1.66/0.62    inference(avatar_component_clause,[],[f304])).
% 1.66/0.62  fof(f306,plain,(
% 1.66/0.62    spl4_40 | ~spl4_11 | ~spl4_37),
% 1.66/0.62    inference(avatar_split_clause,[],[f296,f286,f104,f304])).
% 1.66/0.62  fof(f286,plain,(
% 1.66/0.62    spl4_37 <=> sK0 = k2_xboole_0(k1_xboole_0,sK0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.66/0.62  fof(f296,plain,(
% 1.66/0.62    ( ! [X1] : (~r1_xboole_0(X1,sK0) | r1_xboole_0(X1,k1_xboole_0)) ) | (~spl4_11 | ~spl4_37)),
% 1.66/0.62    inference(superposition,[],[f105,f288])).
% 1.66/0.62  fof(f288,plain,(
% 1.66/0.62    sK0 = k2_xboole_0(k1_xboole_0,sK0) | ~spl4_37),
% 1.66/0.62    inference(avatar_component_clause,[],[f286])).
% 1.66/0.62  fof(f289,plain,(
% 1.66/0.62    spl4_37 | ~spl4_26 | ~spl4_34),
% 1.66/0.62    inference(avatar_split_clause,[],[f259,f253,f199,f286])).
% 1.66/0.62  fof(f253,plain,(
% 1.66/0.62    spl4_34 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.66/0.62  fof(f259,plain,(
% 1.66/0.62    sK0 = k2_xboole_0(k1_xboole_0,sK0) | (~spl4_26 | ~spl4_34)),
% 1.66/0.62    inference(superposition,[],[f200,f255])).
% 1.66/0.62  fof(f255,plain,(
% 1.66/0.62    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | ~spl4_34),
% 1.66/0.62    inference(avatar_component_clause,[],[f253])).
% 1.66/0.62  fof(f256,plain,(
% 1.66/0.62    spl4_34 | ~spl4_4 | ~spl4_28),
% 1.66/0.62    inference(avatar_split_clause,[],[f246,f210,f69,f253])).
% 1.66/0.62  fof(f246,plain,(
% 1.66/0.62    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | (~spl4_4 | ~spl4_28)),
% 1.66/0.62    inference(resolution,[],[f211,f71])).
% 1.66/0.62  fof(f251,plain,(
% 1.66/0.62    spl4_33),
% 1.66/0.62    inference(avatar_split_clause,[],[f41,f249])).
% 1.66/0.62  fof(f41,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f19])).
% 1.66/0.62  fof(f19,plain,(
% 1.66/0.62    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.66/0.62    inference(ennf_transformation,[],[f11])).
% 1.66/0.62  fof(f11,axiom,(
% 1.66/0.62    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.66/0.62  fof(f229,plain,(
% 1.66/0.62    spl4_31 | ~spl4_3 | ~spl4_30),
% 1.66/0.62    inference(avatar_split_clause,[],[f224,f220,f65,f226])).
% 1.66/0.62  fof(f220,plain,(
% 1.66/0.62    spl4_30 <=> ! [X0] : (k1_xboole_0 != k4_xboole_0(X0,X0) | r1_xboole_0(X0,k1_xboole_0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.66/0.62  fof(f224,plain,(
% 1.66/0.62    r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_30)),
% 1.66/0.62    inference(trivial_inequality_removal,[],[f223])).
% 1.66/0.62  fof(f223,plain,(
% 1.66/0.62    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_30)),
% 1.66/0.62    inference(superposition,[],[f221,f66])).
% 1.66/0.62  fof(f221,plain,(
% 1.66/0.62    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(X0,X0) | r1_xboole_0(X0,k1_xboole_0)) ) | ~spl4_30),
% 1.66/0.62    inference(avatar_component_clause,[],[f220])).
% 1.66/0.62  fof(f222,plain,(
% 1.66/0.62    spl4_30 | ~spl4_3 | ~spl4_27),
% 1.66/0.62    inference(avatar_split_clause,[],[f218,f206,f65,f220])).
% 1.66/0.62  fof(f206,plain,(
% 1.66/0.62    spl4_27 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.66/0.62  fof(f218,plain,(
% 1.66/0.62    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(X0,X0) | r1_xboole_0(X0,k1_xboole_0)) ) | (~spl4_3 | ~spl4_27)),
% 1.66/0.62    inference(superposition,[],[f207,f66])).
% 1.66/0.62  fof(f207,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) ) | ~spl4_27),
% 1.66/0.62    inference(avatar_component_clause,[],[f206])).
% 1.66/0.62  fof(f212,plain,(
% 1.66/0.62    spl4_28),
% 1.66/0.62    inference(avatar_split_clause,[],[f52,f210])).
% 1.66/0.62  fof(f52,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.66/0.62    inference(definition_unfolding,[],[f39,f34])).
% 1.66/0.62  fof(f39,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f27])).
% 1.66/0.62  fof(f27,plain,(
% 1.66/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.66/0.62    inference(nnf_transformation,[],[f2])).
% 1.66/0.62  fof(f2,axiom,(
% 1.66/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.66/0.62  fof(f208,plain,(
% 1.66/0.62    spl4_27),
% 1.66/0.62    inference(avatar_split_clause,[],[f51,f206])).
% 1.66/0.62  fof(f51,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.66/0.62    inference(definition_unfolding,[],[f40,f34])).
% 1.66/0.62  fof(f40,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.66/0.62    inference(cnf_transformation,[],[f27])).
% 1.66/0.62  fof(f201,plain,(
% 1.66/0.62    spl4_26 | ~spl4_7 | ~spl4_10),
% 1.66/0.62    inference(avatar_split_clause,[],[f112,f100,f85,f199])).
% 1.66/0.62  fof(f100,plain,(
% 1.66/0.62    spl4_10 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.66/0.62  fof(f112,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0) ) | (~spl4_7 | ~spl4_10)),
% 1.66/0.62    inference(resolution,[],[f101,f86])).
% 1.66/0.62  fof(f101,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_10),
% 1.66/0.62    inference(avatar_component_clause,[],[f100])).
% 1.66/0.62  fof(f182,plain,(
% 1.66/0.62    spl4_23),
% 1.66/0.62    inference(avatar_split_clause,[],[f49,f180])).
% 1.66/0.62  fof(f49,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.66/0.62    inference(definition_unfolding,[],[f36,f34])).
% 1.66/0.62  fof(f36,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f26])).
% 1.66/0.62  fof(f170,plain,(
% 1.66/0.62    spl4_21),
% 1.66/0.62    inference(avatar_split_clause,[],[f45,f168])).
% 1.66/0.62  fof(f45,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f22])).
% 1.66/0.62  fof(f22,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.66/0.62    inference(flattening,[],[f21])).
% 1.66/0.62  fof(f21,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.66/0.62    inference(ennf_transformation,[],[f10])).
% 1.66/0.62  fof(f10,axiom,(
% 1.66/0.62    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.66/0.62  fof(f149,plain,(
% 1.66/0.62    spl4_18 | ~spl4_5 | ~spl4_17),
% 1.66/0.62    inference(avatar_split_clause,[],[f144,f141,f74,f147])).
% 1.66/0.62  fof(f141,plain,(
% 1.66/0.62    spl4_17 <=> ! [X1,X0] : (~r1_xboole_0(X1,X0) | r1_xboole_0(X1,k4_xboole_0(X0,X0)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.66/0.62  fof(f144,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X1,X1),X0)) ) | (~spl4_5 | ~spl4_17)),
% 1.66/0.62    inference(resolution,[],[f142,f75])).
% 1.66/0.62  fof(f142,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X0)) | ~r1_xboole_0(X1,X0)) ) | ~spl4_17),
% 1.66/0.62    inference(avatar_component_clause,[],[f141])).
% 1.66/0.62  fof(f143,plain,(
% 1.66/0.62    spl4_17 | ~spl4_11 | ~spl4_16),
% 1.66/0.62    inference(avatar_split_clause,[],[f136,f132,f104,f141])).
% 1.66/0.62  fof(f136,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | r1_xboole_0(X1,k4_xboole_0(X0,X0))) ) | (~spl4_11 | ~spl4_16)),
% 1.66/0.62    inference(superposition,[],[f105,f133])).
% 1.66/0.62  fof(f134,plain,(
% 1.66/0.62    spl4_16 | ~spl4_8 | ~spl4_10),
% 1.66/0.62    inference(avatar_split_clause,[],[f113,f100,f90,f132])).
% 1.66/0.62  fof(f90,plain,(
% 1.66/0.62    spl4_8 <=> ! [X0] : r1_tarski(k4_xboole_0(X0,X0),X0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.66/0.62  fof(f113,plain,(
% 1.66/0.62    ( ! [X2] : (k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2) ) | (~spl4_8 | ~spl4_10)),
% 1.66/0.62    inference(resolution,[],[f101,f91])).
% 1.66/0.62  fof(f91,plain,(
% 1.66/0.62    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,X0),X0)) ) | ~spl4_8),
% 1.66/0.62    inference(avatar_component_clause,[],[f90])).
% 1.66/0.62  fof(f106,plain,(
% 1.66/0.62    spl4_11),
% 1.66/0.62    inference(avatar_split_clause,[],[f42,f104])).
% 1.66/0.62  fof(f42,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f19])).
% 1.66/0.62  fof(f102,plain,(
% 1.66/0.62    spl4_10),
% 1.66/0.62    inference(avatar_split_clause,[],[f37,f100])).
% 1.66/0.62  fof(f37,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f17])).
% 1.66/0.62  fof(f17,plain,(
% 1.66/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f5])).
% 1.66/0.62  fof(f5,axiom,(
% 1.66/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.66/0.62  fof(f92,plain,(
% 1.66/0.62    spl4_8 | ~spl4_3 | ~spl4_7),
% 1.66/0.62    inference(avatar_split_clause,[],[f88,f85,f65,f90])).
% 1.66/0.62  fof(f88,plain,(
% 1.66/0.62    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,X0),X0)) ) | (~spl4_3 | ~spl4_7)),
% 1.66/0.62    inference(superposition,[],[f86,f66])).
% 1.66/0.62  fof(f87,plain,(
% 1.66/0.62    spl4_7),
% 1.66/0.62    inference(avatar_split_clause,[],[f47,f85])).
% 1.66/0.62  fof(f47,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.66/0.62    inference(definition_unfolding,[],[f32,f34])).
% 1.66/0.62  fof(f32,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f6])).
% 1.66/0.62  fof(f6,axiom,(
% 1.66/0.62    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.66/0.62  fof(f82,plain,(
% 1.66/0.62    spl4_6 | ~spl4_4 | ~spl4_5),
% 1.66/0.62    inference(avatar_split_clause,[],[f77,f74,f69,f79])).
% 1.66/0.62  fof(f77,plain,(
% 1.66/0.62    r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) | (~spl4_4 | ~spl4_5)),
% 1.66/0.62    inference(resolution,[],[f75,f71])).
% 1.66/0.62  fof(f76,plain,(
% 1.66/0.62    spl4_5),
% 1.66/0.62    inference(avatar_split_clause,[],[f38,f74])).
% 1.66/0.62  fof(f38,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f18])).
% 1.66/0.62  fof(f18,plain,(
% 1.66/0.62    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f3])).
% 1.66/0.62  fof(f3,axiom,(
% 1.66/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.66/0.62  fof(f72,plain,(
% 1.66/0.62    spl4_4),
% 1.66/0.62    inference(avatar_split_clause,[],[f46,f69])).
% 1.66/0.62  fof(f46,plain,(
% 1.66/0.62    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.66/0.62    inference(definition_unfolding,[],[f30,f34])).
% 1.66/0.62  fof(f30,plain,(
% 1.66/0.62    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.66/0.62    inference(cnf_transformation,[],[f24])).
% 1.66/0.62  fof(f24,plain,(
% 1.66/0.62    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 1.66/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23])).
% 1.66/0.62  fof(f23,plain,(
% 1.66/0.62    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 1.66/0.62    introduced(choice_axiom,[])).
% 1.66/0.62  fof(f15,plain,(
% 1.66/0.62    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f13])).
% 1.66/0.62  fof(f13,negated_conjecture,(
% 1.66/0.62    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.66/0.62    inference(negated_conjecture,[],[f12])).
% 1.66/0.62  fof(f12,conjecture,(
% 1.66/0.62    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 1.66/0.62  fof(f67,plain,(
% 1.66/0.62    spl4_3),
% 1.66/0.62    inference(avatar_split_clause,[],[f31,f65])).
% 1.66/0.62  fof(f31,plain,(
% 1.66/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.62    inference(cnf_transformation,[],[f8])).
% 1.66/0.62  fof(f8,axiom,(
% 1.66/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.66/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.66/0.62  fof(f63,plain,(
% 1.66/0.62    spl4_2),
% 1.66/0.62    inference(avatar_split_clause,[],[f29,f60])).
% 1.66/0.62  fof(f29,plain,(
% 1.66/0.62    r1_tarski(sK0,sK2)),
% 1.66/0.62    inference(cnf_transformation,[],[f24])).
% 1.66/0.62  fof(f58,plain,(
% 1.66/0.62    ~spl4_1),
% 1.66/0.62    inference(avatar_split_clause,[],[f28,f55])).
% 1.66/0.62  fof(f28,plain,(
% 1.66/0.62    ~r1_xboole_0(sK0,sK1)),
% 1.66/0.62    inference(cnf_transformation,[],[f24])).
% 1.66/0.62  % SZS output end Proof for theBenchmark
% 1.66/0.62  % (19019)------------------------------
% 1.66/0.62  % (19019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (19019)Termination reason: Refutation
% 1.66/0.62  
% 1.66/0.62  % (19019)Memory used [KB]: 9466
% 1.66/0.62  % (19019)Time elapsed: 0.193 s
% 1.66/0.62  % (19019)------------------------------
% 1.66/0.62  % (19019)------------------------------
% 1.66/0.62  % (19011)Success in time 0.261 s
%------------------------------------------------------------------------------
