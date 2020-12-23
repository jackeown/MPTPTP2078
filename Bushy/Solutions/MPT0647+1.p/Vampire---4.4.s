%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t54_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:24 EDT 2019

% Result     : Theorem 2.45s
% Output     : Refutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  410 (1139 expanded)
%              Number of leaves         :   91 ( 483 expanded)
%              Depth                    :   16
%              Number of atoms          : 1632 (7531 expanded)
%              Number of equality atoms :  382 (2651 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24949,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f154,f161,f168,f175,f182,f217,f242,f251,f264,f271,f278,f289,f297,f312,f324,f337,f344,f356,f380,f402,f453,f480,f506,f546,f553,f568,f569,f582,f594,f622,f623,f626,f628,f659,f669,f681,f693,f700,f1505,f2027,f2072,f2660,f3800,f4549,f5703,f5800,f6429,f6572,f7227,f7236,f7871,f7935,f8468,f8549,f8557,f8872,f11212,f19275,f19895,f20610,f23140,f23385,f24704,f24715,f24750,f24931,f24932,f24934,f24948])).

fof(f24948,plain,
    ( k1_funct_1(sK0,sK7(sK0,sK1)) != sK6(sK0,sK1)
    | k1_funct_1(k2_funct_1(sK0),sK6(sK0,sK1)) != sK7(sK0,sK1)
    | k1_funct_1(k2_funct_1(sK0),sK6(sK0,sK1)) != k1_xboole_0
    | k1_funct_1(sK1,sK6(sK0,sK1)) != sK7(sK0,sK1)
    | k1_xboole_0 != sK14(sK1,k1_funct_1(sK0,k1_xboole_0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK0,k1_xboole_0),k1_xboole_0),sK1)
    | r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1) ),
    introduced(theory_axiom,[])).

fof(f24934,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1)) != sK7(sK0,sK1)
    | ~ r2_hidden(k1_funct_1(sK1,sK6(sK0,sK1)),k1_relat_1(sK0))
    | r2_hidden(sK7(sK0,sK1),k1_relat_1(sK0)) ),
    introduced(theory_axiom,[])).

fof(f24932,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1)) != sK7(sK0,sK1)
    | k1_funct_1(sK0,k1_funct_1(sK1,sK6(sK0,sK1))) != sK6(sK0,sK1)
    | ~ r2_hidden(k4_tarski(sK7(sK0,sK1),k1_funct_1(sK0,sK7(sK0,sK1))),sK0)
    | r2_hidden(k4_tarski(sK7(sK0,sK1),sK6(sK0,sK1)),sK0) ),
    introduced(theory_axiom,[])).

fof(f24931,plain,
    ( spl15_2330
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_478 ),
    inference(avatar_split_clause,[],[f8505,f5701,f159,f152,f24929])).

fof(f24929,plain,
    ( spl15_2330
  <=> r2_hidden(k4_tarski(sK7(sK0,sK1),k1_funct_1(sK0,sK7(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2330])])).

fof(f152,plain,
    ( spl15_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_0])])).

fof(f159,plain,
    ( spl15_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f5701,plain,
    ( spl15_478
  <=> r2_hidden(sK7(sK0,sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_478])])).

fof(f8505,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1),k1_funct_1(sK0,sK7(sK0,sK1))),sK0)
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_478 ),
    inference(subsumption_resolution,[],[f8504,f153])).

fof(f153,plain,
    ( v1_relat_1(sK0)
    | ~ spl15_0 ),
    inference(avatar_component_clause,[],[f152])).

fof(f8504,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1),k1_funct_1(sK0,sK7(sK0,sK1))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl15_2
    | ~ spl15_478 ),
    inference(subsumption_resolution,[],[f8498,f160])).

fof(f160,plain,
    ( v1_funct_1(sK0)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f159])).

fof(f8498,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1),k1_funct_1(sK0,sK7(sK0,sK1))),sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl15_478 ),
    inference(resolution,[],[f5702,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t54_funct_1.p',d4_funct_1)).

fof(f5702,plain,
    ( r2_hidden(sK7(sK0,sK1),k1_relat_1(sK0))
    | ~ spl15_478 ),
    inference(avatar_component_clause,[],[f5701])).

fof(f24750,plain,
    ( spl15_119
    | ~ spl15_488
    | ~ spl15_1864
    | ~ spl15_2252 ),
    inference(avatar_contradiction_clause,[],[f24749])).

fof(f24749,plain,
    ( $false
    | ~ spl15_119
    | ~ spl15_488
    | ~ spl15_1864
    | ~ spl15_2252 ),
    inference(subsumption_resolution,[],[f24748,f5799])).

fof(f5799,plain,
    ( r2_hidden(sK6(sK0,sK1),k1_relat_1(sK1))
    | ~ spl15_488 ),
    inference(avatar_component_clause,[],[f5798])).

fof(f5798,plain,
    ( spl15_488
  <=> r2_hidden(sK6(sK0,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_488])])).

fof(f24748,plain,
    ( ~ r2_hidden(sK6(sK0,sK1),k1_relat_1(sK1))
    | ~ spl15_119
    | ~ spl15_1864
    | ~ spl15_2252 ),
    inference(subsumption_resolution,[],[f24744,f890])).

fof(f890,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_relat_1(sK0))
    | ~ spl15_119 ),
    inference(avatar_component_clause,[],[f889])).

fof(f889,plain,
    ( spl15_119
  <=> ~ r2_hidden(k1_xboole_0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_119])])).

fof(f24744,plain,
    ( r2_hidden(k1_xboole_0,k1_relat_1(sK0))
    | ~ r2_hidden(sK6(sK0,sK1),k1_relat_1(sK1))
    | ~ spl15_1864
    | ~ spl15_2252 ),
    inference(superposition,[],[f20522,f23384])).

fof(f23384,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK6(sK0,sK1)) = k1_xboole_0
    | ~ spl15_2252 ),
    inference(avatar_component_clause,[],[f23383])).

fof(f23383,plain,
    ( spl15_2252
  <=> k1_funct_1(k2_funct_1(sK0),sK6(sK0,sK1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2252])])).

fof(f20522,plain,
    ( ! [X4] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK0),X4),k1_relat_1(sK0))
        | ~ r2_hidden(X4,k1_relat_1(sK1)) )
    | ~ spl15_1864 ),
    inference(avatar_component_clause,[],[f20521])).

fof(f20521,plain,
    ( spl15_1864
  <=> ! [X4] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK0),X4),k1_relat_1(sK0))
        | ~ r2_hidden(X4,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1864])])).

fof(f24715,plain,
    ( ~ spl15_84
    | ~ spl15_478
    | ~ spl15_658
    | spl15_1101 ),
    inference(avatar_contradiction_clause,[],[f24714])).

fof(f24714,plain,
    ( $false
    | ~ spl15_84
    | ~ spl15_478
    | ~ spl15_658
    | ~ spl15_1101 ),
    inference(subsumption_resolution,[],[f24713,f11208])).

fof(f11208,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1)) != sK7(sK0,sK1)
    | ~ spl15_1101 ),
    inference(avatar_component_clause,[],[f11207])).

fof(f11207,plain,
    ( spl15_1101
  <=> k1_funct_1(sK1,sK6(sK0,sK1)) != sK7(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1101])])).

fof(f24713,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1)) = sK7(sK0,sK1)
    | ~ spl15_84
    | ~ spl15_478
    | ~ spl15_658 ),
    inference(forward_demodulation,[],[f8496,f7235])).

fof(f7235,plain,
    ( k1_funct_1(sK0,sK7(sK0,sK1)) = sK6(sK0,sK1)
    | ~ spl15_658 ),
    inference(avatar_component_clause,[],[f7234])).

fof(f7234,plain,
    ( spl15_658
  <=> k1_funct_1(sK0,sK7(sK0,sK1)) = sK6(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_658])])).

fof(f8496,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,sK7(sK0,sK1))) = sK7(sK0,sK1)
    | ~ spl15_84
    | ~ spl15_478 ),
    inference(resolution,[],[f5702,f668])).

fof(f668,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK0))
        | k1_funct_1(sK1,k1_funct_1(sK0,X5)) = X5 )
    | ~ spl15_84 ),
    inference(avatar_component_clause,[],[f667])).

fof(f667,plain,
    ( spl15_84
  <=> ! [X5] :
        ( k1_funct_1(sK1,k1_funct_1(sK0,X5)) = X5
        | ~ r2_hidden(X5,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_84])])).

fof(f24704,plain,
    ( spl15_2318
    | ~ spl15_90
    | ~ spl15_488 ),
    inference(avatar_split_clause,[],[f8469,f5798,f691,f24702])).

fof(f24702,plain,
    ( spl15_2318
  <=> k1_funct_1(sK0,k1_funct_1(sK1,sK6(sK0,sK1))) = sK6(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2318])])).

fof(f691,plain,
    ( spl15_90
  <=> ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | k1_funct_1(sK0,k1_funct_1(sK1,X4)) = X4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_90])])).

fof(f8469,plain,
    ( k1_funct_1(sK0,k1_funct_1(sK1,sK6(sK0,sK1))) = sK6(sK0,sK1)
    | ~ spl15_90
    | ~ spl15_488 ),
    inference(resolution,[],[f5799,f692])).

fof(f692,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | k1_funct_1(sK0,k1_funct_1(sK1,X4)) = X4 )
    | ~ spl15_90 ),
    inference(avatar_component_clause,[],[f691])).

fof(f23385,plain,
    ( spl15_2252
    | spl15_441
    | ~ spl15_1100
    | ~ spl15_2100 ),
    inference(avatar_split_clause,[],[f23374,f22630,f11210,f4538,f23383])).

fof(f4538,plain,
    ( spl15_441
  <=> ~ r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_441])])).

fof(f11210,plain,
    ( spl15_1100
  <=> k1_funct_1(sK1,sK6(sK0,sK1)) = sK7(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1100])])).

fof(f22630,plain,
    ( spl15_2100
  <=> ! [X3] :
        ( k1_funct_1(k2_funct_1(sK0),X3) = k1_xboole_0
        | r2_hidden(k4_tarski(X3,k1_funct_1(sK1,X3)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2100])])).

fof(f23374,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK6(sK0,sK1)) = k1_xboole_0
    | ~ spl15_441
    | ~ spl15_1100
    | ~ spl15_2100 ),
    inference(subsumption_resolution,[],[f23362,f4539])).

fof(f4539,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ spl15_441 ),
    inference(avatar_component_clause,[],[f4538])).

fof(f23362,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | k1_funct_1(k2_funct_1(sK0),sK6(sK0,sK1)) = k1_xboole_0
    | ~ spl15_1100
    | ~ spl15_2100 ),
    inference(superposition,[],[f22631,f11211])).

fof(f11211,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1)) = sK7(sK0,sK1)
    | ~ spl15_1100 ),
    inference(avatar_component_clause,[],[f11210])).

fof(f22631,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(X3,k1_funct_1(sK1,X3)),sK1)
        | k1_funct_1(k2_funct_1(sK0),X3) = k1_xboole_0 )
    | ~ spl15_2100 ),
    inference(avatar_component_clause,[],[f22630])).

fof(f23140,plain,
    ( spl15_2100
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_224 ),
    inference(avatar_split_clause,[],[f9240,f2025,f180,f173,f22630])).

fof(f173,plain,
    ( spl15_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f180,plain,
    ( spl15_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f2025,plain,
    ( spl15_224
  <=> ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK0),X0) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_224])])).

fof(f9240,plain,
    ( ! [X3] :
        ( k1_funct_1(k2_funct_1(sK0),X3) = k1_xboole_0
        | r2_hidden(k4_tarski(X3,k1_funct_1(sK1,X3)),sK1) )
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_224 ),
    inference(subsumption_resolution,[],[f9239,f174])).

fof(f174,plain,
    ( v1_relat_1(sK1)
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f173])).

fof(f9239,plain,
    ( ! [X3] :
        ( k1_funct_1(k2_funct_1(sK0),X3) = k1_xboole_0
        | r2_hidden(k4_tarski(X3,k1_funct_1(sK1,X3)),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl15_8
    | ~ spl15_224 ),
    inference(subsumption_resolution,[],[f9220,f181])).

fof(f181,plain,
    ( v1_funct_1(sK1)
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f180])).

fof(f9220,plain,
    ( ! [X3] :
        ( k1_funct_1(k2_funct_1(sK0),X3) = k1_xboole_0
        | r2_hidden(k4_tarski(X3,k1_funct_1(sK1,X3)),sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl15_224 ),
    inference(resolution,[],[f2026,f141])).

fof(f2026,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK0),X0) = k1_xboole_0 )
    | ~ spl15_224 ),
    inference(avatar_component_clause,[],[f2025])).

fof(f20610,plain,
    ( spl15_1864
    | ~ spl15_92
    | ~ spl15_550 ),
    inference(avatar_split_clause,[],[f9253,f6389,f698,f20521])).

fof(f698,plain,
    ( spl15_92
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_92])])).

fof(f6389,plain,
    ( spl15_550
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(k2_funct_1(sK0),X0)),k2_funct_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_550])])).

fof(f9253,plain,
    ( ! [X4] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK0),X4),k1_relat_1(sK0))
        | ~ r2_hidden(X4,k1_relat_1(sK1)) )
    | ~ spl15_92
    | ~ spl15_550 ),
    inference(forward_demodulation,[],[f9245,f699])).

fof(f699,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl15_92 ),
    inference(avatar_component_clause,[],[f698])).

fof(f9245,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(k2_funct_1(sK0),X4),k2_relat_1(k2_funct_1(sK0))) )
    | ~ spl15_550 ),
    inference(resolution,[],[f6390,f142])).

fof(f142,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f66,f69,f68,f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t54_funct_1.p',d5_relat_1)).

fof(f6390,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(k2_funct_1(sK0),X0)),k2_funct_1(sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl15_550 ),
    inference(avatar_component_clause,[],[f6389])).

fof(f19895,plain,
    ( spl15_1778
    | ~ spl15_36
    | ~ spl15_422
    | ~ spl15_1738 ),
    inference(avatar_split_clause,[],[f19411,f19273,f3786,f310,f19893])).

fof(f19893,plain,
    ( spl15_1778
  <=> k1_funct_1(k2_funct_1(sK0),sK6(sK0,sK1)) = sK7(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1778])])).

fof(f310,plain,
    ( spl15_36
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_36])])).

fof(f3786,plain,
    ( spl15_422
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_422])])).

fof(f19273,plain,
    ( spl15_1738
  <=> r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1738])])).

fof(f19411,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK6(sK0,sK1)) = sK7(sK0,sK1)
    | ~ spl15_36
    | ~ spl15_422
    | ~ spl15_1738 ),
    inference(subsumption_resolution,[],[f19410,f311])).

fof(f311,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl15_36 ),
    inference(avatar_component_clause,[],[f310])).

fof(f19410,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK6(sK0,sK1)) = sK7(sK0,sK1)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl15_422
    | ~ spl15_1738 ),
    inference(subsumption_resolution,[],[f19404,f3787])).

fof(f3787,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl15_422 ),
    inference(avatar_component_clause,[],[f3786])).

fof(f19404,plain,
    ( k1_funct_1(k2_funct_1(sK0),sK6(sK0,sK1)) = sK7(sK0,sK1)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl15_1738 ),
    inference(resolution,[],[f19274,f413])).

fof(f413,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) = X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f114,f144])).

fof(f144,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK12(X0,X1),X3),X0)
            | ~ r2_hidden(sK12(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK12(X0,X1),sK13(X0,X1)),X0)
            | r2_hidden(sK12(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK14(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f72,f75,f74,f73])).

fof(f73,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK12(X0,X1),X3),X0)
          | ~ r2_hidden(sK12(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK12(X0,X1),X4),X0)
          | r2_hidden(sK12(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK13(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK14(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t54_funct_1.p',d4_relat_1)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f19274,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),k2_funct_1(sK0))
    | ~ spl15_1738 ),
    inference(avatar_component_clause,[],[f19273])).

fof(f19275,plain,
    ( spl15_1738
    | ~ spl15_232
    | ~ spl15_442 ),
    inference(avatar_split_clause,[],[f15941,f4547,f2070,f19273])).

fof(f2070,plain,
    ( spl15_232
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | r2_hidden(k4_tarski(X1,X0),k2_funct_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_232])])).

fof(f4547,plain,
    ( spl15_442
  <=> r2_hidden(k4_tarski(sK7(sK0,sK1),sK6(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_442])])).

fof(f15941,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),k2_funct_1(sK0))
    | ~ spl15_232
    | ~ spl15_442 ),
    inference(resolution,[],[f4548,f2071])).

fof(f2071,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | r2_hidden(k4_tarski(X1,X0),k2_funct_1(sK0)) )
    | ~ spl15_232 ),
    inference(avatar_component_clause,[],[f2070])).

fof(f4548,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1),sK6(sK0,sK1)),sK0)
    | ~ spl15_442 ),
    inference(avatar_component_clause,[],[f4547])).

fof(f11212,plain,
    ( spl15_1100
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_440 ),
    inference(avatar_split_clause,[],[f8460,f4541,f180,f173,f11210])).

fof(f4541,plain,
    ( spl15_440
  <=> r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_440])])).

fof(f8460,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1)) = sK7(sK0,sK1)
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_440 ),
    inference(subsumption_resolution,[],[f8459,f174])).

fof(f8459,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1)) = sK7(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl15_8
    | ~ spl15_440 ),
    inference(subsumption_resolution,[],[f8452,f181])).

fof(f8452,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1)) = sK7(sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl15_440 ),
    inference(resolution,[],[f4542,f413])).

fof(f4542,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ spl15_440 ),
    inference(avatar_component_clause,[],[f4541])).

fof(f8872,plain,
    ( spl15_834
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_748
    | ~ spl15_806 ),
    inference(avatar_split_clause,[],[f8604,f8547,f7933,f180,f173,f8870])).

fof(f8870,plain,
    ( spl15_834
  <=> k1_xboole_0 = sK14(sK1,k1_funct_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_834])])).

fof(f7933,plain,
    ( spl15_748
  <=> k1_funct_1(sK1,k1_funct_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_748])])).

fof(f8547,plain,
    ( spl15_806
  <=> r2_hidden(k4_tarski(k1_funct_1(sK0,k1_xboole_0),sK14(sK1,k1_funct_1(sK0,k1_xboole_0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_806])])).

fof(f8604,plain,
    ( k1_xboole_0 = sK14(sK1,k1_funct_1(sK0,k1_xboole_0))
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_748
    | ~ spl15_806 ),
    inference(forward_demodulation,[],[f8603,f7934])).

fof(f7934,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,k1_xboole_0)) = k1_xboole_0
    | ~ spl15_748 ),
    inference(avatar_component_clause,[],[f7933])).

fof(f8603,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,k1_xboole_0)) = sK14(sK1,k1_funct_1(sK0,k1_xboole_0))
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_806 ),
    inference(subsumption_resolution,[],[f8602,f174])).

fof(f8602,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,k1_xboole_0)) = sK14(sK1,k1_funct_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK1)
    | ~ spl15_8
    | ~ spl15_806 ),
    inference(subsumption_resolution,[],[f8596,f181])).

fof(f8596,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,k1_xboole_0)) = sK14(sK1,k1_funct_1(sK0,k1_xboole_0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl15_806 ),
    inference(resolution,[],[f8548,f413])).

fof(f8548,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,k1_xboole_0),sK14(sK1,k1_funct_1(sK0,k1_xboole_0))),sK1)
    | ~ spl15_806 ),
    inference(avatar_component_clause,[],[f8547])).

fof(f8557,plain,
    ( spl15_808
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_744
    | ~ spl15_748 ),
    inference(avatar_split_clause,[],[f8550,f7933,f7869,f180,f173,f8555])).

fof(f8555,plain,
    ( spl15_808
  <=> r2_hidden(k4_tarski(k1_funct_1(sK0,k1_xboole_0),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_808])])).

fof(f7869,plain,
    ( spl15_744
  <=> r2_hidden(k1_funct_1(sK0,k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_744])])).

fof(f8550,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,k1_xboole_0),k1_xboole_0),sK1)
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_744
    | ~ spl15_748 ),
    inference(forward_demodulation,[],[f7887,f7934])).

fof(f7887,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,k1_xboole_0),k1_funct_1(sK1,k1_funct_1(sK0,k1_xboole_0))),sK1)
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_744 ),
    inference(subsumption_resolution,[],[f7886,f174])).

fof(f7886,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,k1_xboole_0),k1_funct_1(sK1,k1_funct_1(sK0,k1_xboole_0))),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl15_8
    | ~ spl15_744 ),
    inference(subsumption_resolution,[],[f7882,f181])).

fof(f7882,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,k1_xboole_0),k1_funct_1(sK1,k1_funct_1(sK0,k1_xboole_0))),sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl15_744 ),
    inference(resolution,[],[f7870,f141])).

fof(f7870,plain,
    ( r2_hidden(k1_funct_1(sK0,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl15_744 ),
    inference(avatar_component_clause,[],[f7869])).

fof(f8549,plain,
    ( spl15_806
    | ~ spl15_744 ),
    inference(avatar_split_clause,[],[f7883,f7869,f8547])).

fof(f7883,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,k1_xboole_0),sK14(sK1,k1_funct_1(sK0,k1_xboole_0))),sK1)
    | ~ spl15_744 ),
    inference(resolution,[],[f7870,f145])).

fof(f145,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK14(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK14(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f8468,plain,
    ( spl15_488
    | ~ spl15_440 ),
    inference(avatar_split_clause,[],[f8454,f4541,f5798])).

fof(f8454,plain,
    ( r2_hidden(sK6(sK0,sK1),k1_relat_1(sK1))
    | ~ spl15_440 ),
    inference(resolution,[],[f4542,f144])).

fof(f7935,plain,
    ( spl15_748
    | ~ spl15_84
    | ~ spl15_118 ),
    inference(avatar_split_clause,[],[f7798,f886,f667,f7933])).

fof(f886,plain,
    ( spl15_118
  <=> r2_hidden(k1_xboole_0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_118])])).

fof(f7798,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,k1_xboole_0)) = k1_xboole_0
    | ~ spl15_84
    | ~ spl15_118 ),
    inference(resolution,[],[f887,f668])).

fof(f887,plain,
    ( r2_hidden(k1_xboole_0,k1_relat_1(sK0))
    | ~ spl15_118 ),
    inference(avatar_component_clause,[],[f886])).

fof(f7871,plain,
    ( spl15_744
    | ~ spl15_38
    | ~ spl15_118 ),
    inference(avatar_split_clause,[],[f7799,f886,f322,f7869])).

fof(f322,plain,
    ( spl15_38
  <=> ! [X5] :
        ( r2_hidden(k1_funct_1(sK0,X5),k1_relat_1(sK1))
        | ~ r2_hidden(X5,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_38])])).

fof(f7799,plain,
    ( r2_hidden(k1_funct_1(sK0,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl15_38
    | ~ spl15_118 ),
    inference(resolution,[],[f887,f323])).

fof(f323,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X5),k1_relat_1(sK1)) )
    | ~ spl15_38 ),
    inference(avatar_component_clause,[],[f322])).

fof(f7236,plain,
    ( spl15_658
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_442 ),
    inference(avatar_split_clause,[],[f4643,f4547,f159,f152,f7234])).

fof(f4643,plain,
    ( k1_funct_1(sK0,sK7(sK0,sK1)) = sK6(sK0,sK1)
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_442 ),
    inference(subsumption_resolution,[],[f4642,f153])).

fof(f4642,plain,
    ( k1_funct_1(sK0,sK7(sK0,sK1)) = sK6(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl15_2
    | ~ spl15_442 ),
    inference(subsumption_resolution,[],[f4633,f160])).

fof(f4633,plain,
    ( k1_funct_1(sK0,sK7(sK0,sK1)) = sK6(sK0,sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl15_442 ),
    inference(resolution,[],[f4548,f413])).

fof(f7227,plain,
    ( ~ spl15_441
    | ~ spl15_0
    | ~ spl15_6
    | spl15_43
    | ~ spl15_442 ),
    inference(avatar_split_clause,[],[f4641,f4547,f339,f173,f152,f4538])).

fof(f339,plain,
    ( spl15_43
  <=> k4_relat_1(sK0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_43])])).

fof(f4641,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ spl15_0
    | ~ spl15_6
    | ~ spl15_43
    | ~ spl15_442 ),
    inference(subsumption_resolution,[],[f4640,f153])).

fof(f4640,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl15_6
    | ~ spl15_43
    | ~ spl15_442 ),
    inference(subsumption_resolution,[],[f4639,f174])).

fof(f4639,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl15_43
    | ~ spl15_442 ),
    inference(subsumption_resolution,[],[f4631,f340])).

fof(f340,plain,
    ( k4_relat_1(sK0) != sK1
    | ~ spl15_43 ),
    inference(avatar_component_clause,[],[f339])).

fof(f4631,plain,
    ( k4_relat_1(sK0) = sK1
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl15_442 ),
    inference(resolution,[],[f4548,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
      | k4_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t54_funct_1.p',d7_relat_1)).

fof(f6572,plain,
    ( spl15_568
    | ~ spl15_82
    | ~ spl15_488 ),
    inference(avatar_split_clause,[],[f5838,f5798,f657,f6570])).

fof(f6570,plain,
    ( spl15_568
  <=> r2_hidden(k1_funct_1(sK1,sK6(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_568])])).

fof(f657,plain,
    ( spl15_82
  <=> ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK1,X4),k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_82])])).

fof(f5838,plain,
    ( r2_hidden(k1_funct_1(sK1,sK6(sK0,sK1)),k1_relat_1(sK0))
    | ~ spl15_82
    | ~ spl15_488 ),
    inference(resolution,[],[f5799,f658])).

fof(f658,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK1,X4),k1_relat_1(sK0)) )
    | ~ spl15_82 ),
    inference(avatar_component_clause,[],[f657])).

fof(f6429,plain,
    ( spl15_550
    | ~ spl15_36
    | ~ spl15_86
    | ~ spl15_422 ),
    inference(avatar_split_clause,[],[f5071,f3786,f679,f310,f6389])).

fof(f679,plain,
    ( spl15_86
  <=> k1_relat_1(sK1) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_86])])).

fof(f5071,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(k2_funct_1(sK0),X0)),k2_funct_1(sK0)) )
    | ~ spl15_36
    | ~ spl15_86
    | ~ spl15_422 ),
    inference(subsumption_resolution,[],[f5070,f311])).

fof(f5070,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(k2_funct_1(sK0),X0)),k2_funct_1(sK0))
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl15_86
    | ~ spl15_422 ),
    inference(subsumption_resolution,[],[f5052,f3787])).

fof(f5052,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(k2_funct_1(sK0),X0)),k2_funct_1(sK0))
        | ~ v1_funct_1(k2_funct_1(sK0))
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl15_86 ),
    inference(superposition,[],[f141,f680])).

fof(f680,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl15_86 ),
    inference(avatar_component_clause,[],[f679])).

fof(f5800,plain,
    ( spl15_488
    | ~ spl15_26
    | ~ spl15_442 ),
    inference(avatar_split_clause,[],[f5704,f4547,f262,f5798])).

fof(f262,plain,
    ( spl15_26
  <=> k1_relat_1(sK1) = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_26])])).

fof(f5704,plain,
    ( r2_hidden(sK6(sK0,sK1),k1_relat_1(sK1))
    | ~ spl15_26
    | ~ spl15_442 ),
    inference(forward_demodulation,[],[f4636,f263])).

fof(f263,plain,
    ( k1_relat_1(sK1) = k2_relat_1(sK0)
    | ~ spl15_26 ),
    inference(avatar_component_clause,[],[f262])).

fof(f4636,plain,
    ( r2_hidden(sK6(sK0,sK1),k2_relat_1(sK0))
    | ~ spl15_442 ),
    inference(resolution,[],[f4548,f142])).

fof(f5703,plain,
    ( spl15_478
    | ~ spl15_442 ),
    inference(avatar_split_clause,[],[f4635,f4547,f5701])).

fof(f4635,plain,
    ( r2_hidden(sK7(sK0,sK1),k1_relat_1(sK0))
    | ~ spl15_442 ),
    inference(resolution,[],[f4548,f144])).

fof(f4549,plain,
    ( spl15_440
    | spl15_442
    | ~ spl15_6
    | spl15_25
    | ~ spl15_174 ),
    inference(avatar_split_clause,[],[f1534,f1503,f253,f173,f4547,f4541])).

fof(f253,plain,
    ( spl15_25
  <=> k2_funct_1(sK0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_25])])).

fof(f1503,plain,
    ( spl15_174
  <=> ! [X4] :
        ( k2_funct_1(sK0) = X4
        | r2_hidden(k4_tarski(sK7(sK0,X4),sK6(sK0,X4)),sK0)
        | r2_hidden(k4_tarski(sK6(sK0,X4),sK7(sK0,X4)),X4)
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_174])])).

fof(f1534,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1),sK6(sK0,sK1)),sK0)
    | r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | ~ spl15_6
    | ~ spl15_25
    | ~ spl15_174 ),
    inference(subsumption_resolution,[],[f1533,f254])).

fof(f254,plain,
    ( k2_funct_1(sK0) != sK1
    | ~ spl15_25 ),
    inference(avatar_component_clause,[],[f253])).

fof(f1533,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,sK1),sK6(sK0,sK1)),sK0)
    | r2_hidden(k4_tarski(sK6(sK0,sK1),sK7(sK0,sK1)),sK1)
    | k2_funct_1(sK0) = sK1
    | ~ spl15_6
    | ~ spl15_174 ),
    inference(resolution,[],[f1504,f174])).

fof(f1504,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(X4)
        | r2_hidden(k4_tarski(sK7(sK0,X4),sK6(sK0,X4)),sK0)
        | r2_hidden(k4_tarski(sK6(sK0,X4),sK7(sK0,X4)),X4)
        | k2_funct_1(sK0) = X4 )
    | ~ spl15_174 ),
    inference(avatar_component_clause,[],[f1503])).

fof(f3800,plain,
    ( ~ spl15_0
    | ~ spl15_2
    | spl15_423 ),
    inference(avatar_contradiction_clause,[],[f3799])).

fof(f3799,plain,
    ( $false
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_423 ),
    inference(subsumption_resolution,[],[f3798,f153])).

fof(f3798,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl15_2
    | ~ spl15_423 ),
    inference(subsumption_resolution,[],[f3796,f160])).

fof(f3796,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl15_423 ),
    inference(resolution,[],[f3790,f111])).

fof(f111,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t54_funct_1.p',dt_k2_funct_1)).

fof(f3790,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ spl15_423 ),
    inference(avatar_component_clause,[],[f3789])).

fof(f3789,plain,
    ( spl15_423
  <=> ~ v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_423])])).

fof(f2660,plain,
    ( k2_funct_1(sK0) != k4_relat_1(sK0)
    | k2_funct_1(sK0) != sK1
    | k4_relat_1(k4_relat_1(sK0)) != sK0
    | k1_relat_1(sK1) != k2_relat_1(k4_relat_1(sK1))
    | k1_relat_1(sK1) = k2_relat_1(sK0) ),
    introduced(theory_axiom,[])).

fof(f2072,plain,
    ( spl15_232
    | ~ spl15_34
    | ~ spl15_36 ),
    inference(avatar_split_clause,[],[f650,f310,f295,f2070])).

fof(f295,plain,
    ( spl15_34
  <=> k4_relat_1(k2_funct_1(sK0)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_34])])).

fof(f650,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | r2_hidden(k4_tarski(X1,X0),k2_funct_1(sK0)) )
    | ~ spl15_34
    | ~ spl15_36 ),
    inference(subsumption_resolution,[],[f648,f311])).

fof(f648,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | r2_hidden(k4_tarski(X1,X0),k2_funct_1(sK0))
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl15_34 ),
    inference(superposition,[],[f358,f296])).

fof(f296,plain,
    ( k4_relat_1(k2_funct_1(sK0)) = sK0
    | ~ spl15_34 ),
    inference(avatar_component_clause,[],[f295])).

fof(f358,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f138,f98])).

fof(f98,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t54_funct_1.p',dt_k4_relat_1)).

fof(f138,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2027,plain,
    ( spl15_224
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_86 ),
    inference(avatar_split_clause,[],[f998,f679,f159,f152,f2025])).

fof(f998,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK0),X0) = k1_xboole_0 )
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_86 ),
    inference(forward_demodulation,[],[f997,f680])).

fof(f997,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK0),X0) = k1_xboole_0
        | r2_hidden(X0,k1_relat_1(k2_funct_1(sK0))) )
    | ~ spl15_0
    | ~ spl15_2 ),
    inference(subsumption_resolution,[],[f994,f153])).

fof(f994,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK0),X0) = k1_xboole_0
        | r2_hidden(X0,k1_relat_1(k2_funct_1(sK0)))
        | ~ v1_relat_1(sK0) )
    | ~ spl15_2 ),
    inference(resolution,[],[f305,f160])).

fof(f305,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X3)
      | k1_funct_1(k2_funct_1(X3),X2) = k1_xboole_0
      | r2_hidden(X2,k1_relat_1(k2_funct_1(X3)))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f302,f110])).

fof(f110,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f302,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k1_relat_1(k2_funct_1(X3)))
      | k1_funct_1(k2_funct_1(X3),X2) = k1_xboole_0
      | ~ v1_relat_1(k2_funct_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f139,f111])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1505,plain,
    ( spl15_174
    | ~ spl15_0
    | ~ spl15_32 ),
    inference(avatar_split_clause,[],[f1494,f287,f152,f1503])).

fof(f287,plain,
    ( spl15_32
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_32])])).

fof(f1494,plain,
    ( ! [X4] :
        ( k2_funct_1(sK0) = X4
        | r2_hidden(k4_tarski(sK7(sK0,X4),sK6(sK0,X4)),sK0)
        | r2_hidden(k4_tarski(sK6(sK0,X4),sK7(sK0,X4)),X4)
        | ~ v1_relat_1(X4) )
    | ~ spl15_0
    | ~ spl15_32 ),
    inference(forward_demodulation,[],[f476,f288])).

fof(f288,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl15_32 ),
    inference(avatar_component_clause,[],[f287])).

fof(f476,plain,
    ( ! [X4] :
        ( r2_hidden(k4_tarski(sK7(sK0,X4),sK6(sK0,X4)),sK0)
        | r2_hidden(k4_tarski(sK6(sK0,X4),sK7(sK0,X4)),X4)
        | ~ v1_relat_1(X4)
        | k4_relat_1(sK0) = X4 )
    | ~ spl15_0 ),
    inference(resolution,[],[f108,f153])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | k4_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f700,plain,
    ( spl15_92
    | ~ spl15_28
    | ~ spl15_32 ),
    inference(avatar_split_clause,[],[f665,f287,f269,f698])).

fof(f269,plain,
    ( spl15_28
  <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_28])])).

fof(f665,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl15_28
    | ~ spl15_32 ),
    inference(forward_demodulation,[],[f270,f288])).

fof(f270,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl15_28 ),
    inference(avatar_component_clause,[],[f269])).

fof(f693,plain,
    ( spl15_90
    | spl15_25
    | ~ spl15_26 ),
    inference(avatar_split_clause,[],[f682,f262,f253,f691])).

fof(f682,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | k1_funct_1(sK0,k1_funct_1(sK1,X4)) = X4 )
    | ~ spl15_25
    | ~ spl15_26 ),
    inference(subsumption_resolution,[],[f633,f254])).

fof(f633,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | k1_funct_1(sK0,k1_funct_1(sK1,X4)) = X4
        | k2_funct_1(sK0) = sK1 )
    | ~ spl15_26 ),
    inference(forward_demodulation,[],[f133,f263])).

fof(f133,plain,(
    ! [X4] :
      ( k1_funct_1(sK0,k1_funct_1(sK1,X4)) = X4
      | ~ r2_hidden(X4,k2_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK0,X5) = X4
      | k1_funct_1(sK1,X4) != X5
      | ~ r2_hidden(X4,k2_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( ( ( k1_funct_1(sK1,sK2) != sK3
          | ~ r2_hidden(sK2,k2_relat_1(sK0)) )
        & k1_funct_1(sK0,sK3) = sK2
        & r2_hidden(sK3,k1_relat_1(sK0)) )
      | ( ( k1_funct_1(sK0,sK3) != sK2
          | ~ r2_hidden(sK3,k1_relat_1(sK0)) )
        & k1_funct_1(sK1,sK2) = sK3
        & r2_hidden(sK2,k2_relat_1(sK0)) )
      | k1_relat_1(sK1) != k2_relat_1(sK0)
      | k2_funct_1(sK0) != sK1 )
    & ( ( ! [X4,X5] :
            ( ( ( k1_funct_1(sK1,X4) = X5
                & r2_hidden(X4,k2_relat_1(sK0)) )
              | k1_funct_1(sK0,X5) != X4
              | ~ r2_hidden(X5,k1_relat_1(sK0)) )
            & ( ( k1_funct_1(sK0,X5) = X4
                & r2_hidden(X5,k1_relat_1(sK0)) )
              | k1_funct_1(sK1,X4) != X5
              | ~ r2_hidden(X4,k2_relat_1(sK0)) ) )
        & k1_relat_1(sK1) = k2_relat_1(sK0) )
      | k2_funct_1(sK0) = sK1 )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f52,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0)
              | k2_funct_1(X0) != X1 )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) = X1 )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ? [X3,X2] :
                ( ( ( k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(sK0)) )
                  & k1_funct_1(sK0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(sK0)) )
                | ( ( k1_funct_1(sK0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(sK0)) )
                  & k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(sK0)) ) )
            | k1_relat_1(X1) != k2_relat_1(sK0)
            | k2_funct_1(sK0) != X1 )
          & ( ( ! [X5,X4] :
                  ( ( ( k1_funct_1(X1,X4) = X5
                      & r2_hidden(X4,k2_relat_1(sK0)) )
                    | k1_funct_1(sK0,X5) != X4
                    | ~ r2_hidden(X5,k1_relat_1(sK0)) )
                  & ( ( k1_funct_1(sK0,X5) = X4
                      & r2_hidden(X5,k1_relat_1(sK0)) )
                    | k1_funct_1(X1,X4) != X5
                    | ~ r2_hidden(X4,k2_relat_1(sK0)) ) )
              & k1_relat_1(X1) = k2_relat_1(sK0) )
            | k2_funct_1(sK0) = X1 )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2,X3] :
                ( ( ( k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) )
                  & k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) )
                | ( ( k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(X0)) ) )
            | k1_relat_1(X1) != k2_relat_1(X0)
            | k2_funct_1(X0) != X1 )
          & ( ( ! [X4,X5] :
                  ( ( ( k1_funct_1(X1,X4) = X5
                      & r2_hidden(X4,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X5) != X4
                    | ~ r2_hidden(X5,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X5) = X4
                      & r2_hidden(X5,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X4) != X5
                    | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) )
            | k2_funct_1(X0) = X1 )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ( ? [X3,X2] :
              ( ( ( k1_funct_1(sK1,X2) != X3
                  | ~ r2_hidden(X2,k2_relat_1(X0)) )
                & k1_funct_1(X0,X3) = X2
                & r2_hidden(X3,k1_relat_1(X0)) )
              | ( ( k1_funct_1(X0,X3) != X2
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & k1_funct_1(sK1,X2) = X3
                & r2_hidden(X2,k2_relat_1(X0)) ) )
          | k1_relat_1(sK1) != k2_relat_1(X0)
          | k2_funct_1(X0) != sK1 )
        & ( ( ! [X5,X4] :
                ( ( ( k1_funct_1(sK1,X4) = X5
                    & r2_hidden(X4,k2_relat_1(X0)) )
                  | k1_funct_1(X0,X5) != X4
                  | ~ r2_hidden(X5,k1_relat_1(X0)) )
                & ( ( k1_funct_1(X0,X5) = X4
                    & r2_hidden(X5,k1_relat_1(X0)) )
                  | k1_funct_1(sK1,X4) != X5
                  | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
            & k1_relat_1(sK1) = k2_relat_1(X0) )
          | k2_funct_1(X0) = sK1 )
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ( ( k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & k1_funct_1(X1,X2) = X3
            & r2_hidden(X2,k2_relat_1(X0)) ) )
     => ( ( ( k1_funct_1(X1,sK2) != sK3
            | ~ r2_hidden(sK2,k2_relat_1(X0)) )
          & k1_funct_1(X0,sK3) = sK2
          & r2_hidden(sK3,k1_relat_1(X0)) )
        | ( ( k1_funct_1(X0,sK3) != sK2
            | ~ r2_hidden(sK3,k1_relat_1(X0)) )
          & k1_funct_1(X1,sK2) = sK3
          & r2_hidden(sK2,k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2,X3] :
                ( ( ( k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) )
                  & k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) )
                | ( ( k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(X0)) ) )
            | k1_relat_1(X1) != k2_relat_1(X0)
            | k2_funct_1(X0) != X1 )
          & ( ( ! [X4,X5] :
                  ( ( ( k1_funct_1(X1,X4) = X5
                      & r2_hidden(X4,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X5) != X4
                    | ~ r2_hidden(X5,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X5) = X4
                      & r2_hidden(X5,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X4) != X5
                    | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) )
            | k2_funct_1(X0) = X1 )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2,X3] :
                ( ( ( k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) )
                  & k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) )
                | ( ( k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(X0)) ) )
            | k1_relat_1(X1) != k2_relat_1(X0)
            | k2_funct_1(X0) != X1 )
          & ( ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) )
            | k2_funct_1(X0) = X1 )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2,X3] :
                ( ( ( k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) )
                  & k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) )
                | ( ( k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(X0)) ) )
            | k1_relat_1(X1) != k2_relat_1(X0)
            | k2_funct_1(X0) != X1 )
          & ( ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) )
            | k2_funct_1(X0) = X1 )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_funct_1(X0) = X1
          <~> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_funct_1(X0) = X1
          <~> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ! [X1] :
              ( ( v1_funct_1(X1)
                & v1_relat_1(X1) )
             => ( k2_funct_1(X0) = X1
              <=> ( ! [X2,X3] :
                      ( ( ( k1_funct_1(X0,X3) = X2
                          & r2_hidden(X3,k1_relat_1(X0)) )
                       => ( k1_funct_1(X1,X2) = X3
                          & r2_hidden(X2,k2_relat_1(X0)) ) )
                      & ( ( k1_funct_1(X1,X2) = X3
                          & r2_hidden(X2,k2_relat_1(X0)) )
                       => ( k1_funct_1(X0,X3) = X2
                          & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                  & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t54_funct_1.p',t54_funct_1)).

fof(f681,plain,
    ( spl15_86
    | ~ spl15_20
    | ~ spl15_26
    | ~ spl15_32 ),
    inference(avatar_split_clause,[],[f320,f287,f262,f240,f679])).

fof(f240,plain,
    ( spl15_20
  <=> k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f320,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl15_20
    | ~ spl15_26
    | ~ spl15_32 ),
    inference(forward_demodulation,[],[f319,f288])).

fof(f319,plain,
    ( k1_relat_1(sK1) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl15_20
    | ~ spl15_26 ),
    inference(forward_demodulation,[],[f241,f263])).

fof(f241,plain,
    ( k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0)
    | ~ spl15_20 ),
    inference(avatar_component_clause,[],[f240])).

fof(f669,plain,
    ( spl15_84
    | spl15_25 ),
    inference(avatar_split_clause,[],[f664,f253,f667])).

fof(f664,plain,
    ( ! [X5] :
        ( k1_funct_1(sK1,k1_funct_1(sK0,X5)) = X5
        | ~ r2_hidden(X5,k1_relat_1(sK0)) )
    | ~ spl15_25 ),
    inference(subsumption_resolution,[],[f131,f254])).

fof(f131,plain,(
    ! [X5] :
      ( k1_funct_1(sK1,k1_funct_1(sK0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK1,X4) = X5
      | k1_funct_1(sK0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f659,plain,
    ( spl15_82
    | spl15_25
    | ~ spl15_26 ),
    inference(avatar_split_clause,[],[f655,f262,f253,f657])).

fof(f655,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK1,X4),k1_relat_1(sK0)) )
    | ~ spl15_25
    | ~ spl15_26 ),
    inference(subsumption_resolution,[],[f318,f254])).

fof(f318,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK1,X4),k1_relat_1(sK0))
        | k2_funct_1(sK0) = sK1 )
    | ~ spl15_26 ),
    inference(forward_demodulation,[],[f134,f263])).

fof(f134,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK1,X4),k1_relat_1(sK0))
      | ~ r2_hidden(X4,k2_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,k1_relat_1(sK0))
      | k1_funct_1(sK1,X4) != X5
      | ~ r2_hidden(X4,k2_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f628,plain,
    ( k2_funct_1(sK0) != k4_relat_1(sK0)
    | k4_relat_1(sK0) != sK1
    | k2_funct_1(sK0) = sK1 ),
    introduced(theory_axiom,[])).

fof(f626,plain,
    ( spl15_64
    | ~ spl15_24
    | ~ spl15_26
    | spl15_49 ),
    inference(avatar_split_clause,[],[f625,f375,f262,f256,f501])).

fof(f501,plain,
    ( spl15_64
  <=> k1_funct_1(sK0,sK3) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_64])])).

fof(f256,plain,
    ( spl15_24
  <=> k2_funct_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_24])])).

fof(f375,plain,
    ( spl15_49
  <=> ~ r2_hidden(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_49])])).

fof(f625,plain,
    ( k1_funct_1(sK0,sK3) = sK2
    | ~ spl15_24
    | ~ spl15_26
    | ~ spl15_49 ),
    inference(subsumption_resolution,[],[f412,f376])).

fof(f376,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ spl15_49 ),
    inference(avatar_component_clause,[],[f375])).

fof(f412,plain,
    ( r2_hidden(sK2,k1_relat_1(sK1))
    | k1_funct_1(sK0,sK3) = sK2
    | ~ spl15_24
    | ~ spl15_26 ),
    inference(forward_demodulation,[],[f411,f263])).

fof(f411,plain,
    ( k1_funct_1(sK0,sK3) = sK2
    | r2_hidden(sK2,k2_relat_1(sK0))
    | ~ spl15_24
    | ~ spl15_26 ),
    inference(subsumption_resolution,[],[f410,f257])).

fof(f257,plain,
    ( k2_funct_1(sK0) = sK1
    | ~ spl15_24 ),
    inference(avatar_component_clause,[],[f256])).

fof(f410,plain,
    ( k1_funct_1(sK0,sK3) = sK2
    | r2_hidden(sK2,k2_relat_1(sK0))
    | k2_funct_1(sK0) != sK1
    | ~ spl15_26 ),
    inference(subsumption_resolution,[],[f90,f263])).

fof(f90,plain,
    ( k1_funct_1(sK0,sK3) = sK2
    | r2_hidden(sK2,k2_relat_1(sK0))
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f623,plain,
    ( k1_funct_1(sK0,sK3) != sK2
    | r2_hidden(k4_tarski(sK3,sK2),sK0)
    | ~ r2_hidden(k4_tarski(sK3,k1_funct_1(sK0,sK3)),sK0) ),
    introduced(theory_axiom,[])).

fof(f622,plain,
    ( spl15_58
    | ~ spl15_0
    | ~ spl15_42
    | ~ spl15_72 ),
    inference(avatar_split_clause,[],[f584,f544,f342,f152,f451])).

fof(f451,plain,
    ( spl15_58
  <=> r2_hidden(k4_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_58])])).

fof(f342,plain,
    ( spl15_42
  <=> k4_relat_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_42])])).

fof(f544,plain,
    ( spl15_72
  <=> r2_hidden(k4_tarski(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_72])])).

fof(f584,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),sK1)
    | ~ spl15_0
    | ~ spl15_42
    | ~ spl15_72 ),
    inference(forward_demodulation,[],[f583,f343])).

fof(f343,plain,
    ( k4_relat_1(sK0) = sK1
    | ~ spl15_42 ),
    inference(avatar_component_clause,[],[f342])).

fof(f583,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k4_relat_1(sK0))
    | ~ spl15_0
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f573,f153])).

fof(f573,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl15_72 ),
    inference(resolution,[],[f545,f349])).

fof(f349,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X0)
      | r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f137,f98])).

fof(f137,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f545,plain,
    ( r2_hidden(k4_tarski(sK3,sK2),sK0)
    | ~ spl15_72 ),
    inference(avatar_component_clause,[],[f544])).

fof(f594,plain,
    ( spl15_49
    | ~ spl15_58 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl15_49
    | ~ spl15_58 ),
    inference(unit_resulting_resolution,[],[f452,f376,f144])).

fof(f452,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),sK1)
    | ~ spl15_58 ),
    inference(avatar_component_clause,[],[f451])).

fof(f582,plain,
    ( ~ spl15_0
    | ~ spl15_2
    | spl15_65
    | ~ spl15_72 ),
    inference(avatar_contradiction_clause,[],[f581])).

fof(f581,plain,
    ( $false
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f580,f153])).

fof(f580,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl15_2
    | ~ spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f579,f160])).

fof(f579,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl15_65
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f572,f505])).

fof(f505,plain,
    ( k1_funct_1(sK0,sK3) != sK2
    | ~ spl15_65 ),
    inference(avatar_component_clause,[],[f504])).

fof(f504,plain,
    ( spl15_65
  <=> k1_funct_1(sK0,sK3) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_65])])).

fof(f572,plain,
    ( k1_funct_1(sK0,sK3) = sK2
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl15_72 ),
    inference(resolution,[],[f545,f413])).

fof(f569,plain,
    ( spl15_52
    | ~ spl15_24
    | ~ spl15_26
    | spl15_65 ),
    inference(avatar_split_clause,[],[f566,f504,f262,f256,f400])).

fof(f400,plain,
    ( spl15_52
  <=> k1_funct_1(sK1,sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_52])])).

fof(f566,plain,
    ( k1_funct_1(sK1,sK2) = sK3
    | ~ spl15_24
    | ~ spl15_26
    | ~ spl15_65 ),
    inference(subsumption_resolution,[],[f565,f257])).

fof(f565,plain,
    ( k1_funct_1(sK1,sK2) = sK3
    | k2_funct_1(sK0) != sK1
    | ~ spl15_26
    | ~ spl15_65 ),
    inference(subsumption_resolution,[],[f564,f263])).

fof(f564,plain,
    ( k1_funct_1(sK1,sK2) = sK3
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | k2_funct_1(sK0) != sK1
    | ~ spl15_65 ),
    inference(subsumption_resolution,[],[f91,f505])).

fof(f91,plain,
    ( k1_funct_1(sK0,sK3) = sK2
    | k1_funct_1(sK1,sK2) = sK3
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f568,plain,
    ( ~ spl15_6
    | ~ spl15_8
    | spl15_53
    | ~ spl15_58 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_53
    | ~ spl15_58 ),
    inference(unit_resulting_resolution,[],[f174,f181,f452,f398,f413])).

fof(f398,plain,
    ( k1_funct_1(sK1,sK2) != sK3
    | ~ spl15_53 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl15_53
  <=> k1_funct_1(sK1,sK2) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_53])])).

fof(f553,plain,
    ( spl15_74
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_46 ),
    inference(avatar_split_clause,[],[f486,f372,f159,f152,f551])).

fof(f551,plain,
    ( spl15_74
  <=> r2_hidden(k4_tarski(sK3,k1_funct_1(sK0,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_74])])).

fof(f372,plain,
    ( spl15_46
  <=> r2_hidden(sK3,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_46])])).

fof(f486,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK0,sK3)),sK0)
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f485,f153])).

fof(f485,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK0,sK3)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl15_2
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f481,f160])).

fof(f481,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK0,sK3)),sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl15_46 ),
    inference(resolution,[],[f373,f141])).

fof(f373,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | ~ spl15_46 ),
    inference(avatar_component_clause,[],[f372])).

fof(f546,plain,
    ( spl15_72
    | ~ spl15_6
    | ~ spl15_40
    | ~ spl15_58 ),
    inference(avatar_split_clause,[],[f465,f451,f335,f173,f544])).

fof(f335,plain,
    ( spl15_40
  <=> k4_relat_1(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_40])])).

fof(f465,plain,
    ( r2_hidden(k4_tarski(sK3,sK2),sK0)
    | ~ spl15_6
    | ~ spl15_40
    | ~ spl15_58 ),
    inference(forward_demodulation,[],[f464,f336])).

fof(f336,plain,
    ( k4_relat_1(sK1) = sK0
    | ~ spl15_40 ),
    inference(avatar_component_clause,[],[f335])).

fof(f464,plain,
    ( r2_hidden(k4_tarski(sK3,sK2),k4_relat_1(sK1))
    | ~ spl15_6
    | ~ spl15_58 ),
    inference(subsumption_resolution,[],[f459,f174])).

fof(f459,plain,
    ( r2_hidden(k4_tarski(sK3,sK2),k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl15_58 ),
    inference(resolution,[],[f452,f349])).

fof(f506,plain,
    ( ~ spl15_65
    | ~ spl15_24
    | ~ spl15_26
    | ~ spl15_46
    | ~ spl15_48
    | ~ spl15_52 ),
    inference(avatar_split_clause,[],[f499,f400,f378,f372,f262,f256,f504])).

fof(f378,plain,
    ( spl15_48
  <=> r2_hidden(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_48])])).

fof(f499,plain,
    ( k1_funct_1(sK0,sK3) != sK2
    | ~ spl15_24
    | ~ spl15_26
    | ~ spl15_46
    | ~ spl15_48
    | ~ spl15_52 ),
    inference(subsumption_resolution,[],[f498,f379])).

fof(f379,plain,
    ( r2_hidden(sK2,k1_relat_1(sK1))
    | ~ spl15_48 ),
    inference(avatar_component_clause,[],[f378])).

fof(f498,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | k1_funct_1(sK0,sK3) != sK2
    | ~ spl15_24
    | ~ spl15_26
    | ~ spl15_46
    | ~ spl15_52 ),
    inference(forward_demodulation,[],[f497,f263])).

fof(f497,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK0))
    | k1_funct_1(sK0,sK3) != sK2
    | ~ spl15_24
    | ~ spl15_26
    | ~ spl15_46
    | ~ spl15_52 ),
    inference(subsumption_resolution,[],[f496,f257])).

fof(f496,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK0))
    | k1_funct_1(sK0,sK3) != sK2
    | k2_funct_1(sK0) != sK1
    | ~ spl15_26
    | ~ spl15_46
    | ~ spl15_52 ),
    inference(subsumption_resolution,[],[f495,f263])).

fof(f495,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK0))
    | k1_funct_1(sK0,sK3) != sK2
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | k2_funct_1(sK0) != sK1
    | ~ spl15_46
    | ~ spl15_52 ),
    inference(subsumption_resolution,[],[f494,f373])).

fof(f494,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK0))
    | k1_funct_1(sK0,sK3) != sK2
    | ~ r2_hidden(sK3,k1_relat_1(sK0))
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | k2_funct_1(sK0) != sK1
    | ~ spl15_52 ),
    inference(subsumption_resolution,[],[f95,f401])).

fof(f401,plain,
    ( k1_funct_1(sK1,sK2) = sK3
    | ~ spl15_52 ),
    inference(avatar_component_clause,[],[f400])).

fof(f95,plain,
    ( k1_funct_1(sK1,sK2) != sK3
    | ~ r2_hidden(sK2,k2_relat_1(sK0))
    | k1_funct_1(sK0,sK3) != sK2
    | ~ r2_hidden(sK3,k1_relat_1(sK0))
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f480,plain,
    ( spl15_46
    | ~ spl15_44
    | ~ spl15_58 ),
    inference(avatar_split_clause,[],[f466,f451,f354,f372])).

fof(f354,plain,
    ( spl15_44
  <=> k1_relat_1(sK0) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_44])])).

fof(f466,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | ~ spl15_44
    | ~ spl15_58 ),
    inference(forward_demodulation,[],[f461,f355])).

fof(f355,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ spl15_44 ),
    inference(avatar_component_clause,[],[f354])).

fof(f461,plain,
    ( r2_hidden(sK3,k2_relat_1(sK1))
    | ~ spl15_58 ),
    inference(resolution,[],[f452,f142])).

fof(f453,plain,
    ( spl15_58
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_48
    | ~ spl15_52 ),
    inference(avatar_split_clause,[],[f446,f400,f378,f180,f173,f451])).

fof(f446,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),sK1)
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_48
    | ~ spl15_52 ),
    inference(forward_demodulation,[],[f386,f401])).

fof(f386,plain,
    ( r2_hidden(k4_tarski(sK2,k1_funct_1(sK1,sK2)),sK1)
    | ~ spl15_6
    | ~ spl15_8
    | ~ spl15_48 ),
    inference(subsumption_resolution,[],[f385,f174])).

fof(f385,plain,
    ( r2_hidden(k4_tarski(sK2,k1_funct_1(sK1,sK2)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl15_8
    | ~ spl15_48 ),
    inference(subsumption_resolution,[],[f381,f181])).

fof(f381,plain,
    ( r2_hidden(k4_tarski(sK2,k1_funct_1(sK1,sK2)),sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl15_48 ),
    inference(resolution,[],[f379,f141])).

fof(f402,plain,
    ( spl15_52
    | spl15_46
    | ~ spl15_24
    | ~ spl15_26 ),
    inference(avatar_split_clause,[],[f388,f262,f256,f372,f400])).

fof(f388,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | k1_funct_1(sK1,sK2) = sK3
    | ~ spl15_24
    | ~ spl15_26 ),
    inference(subsumption_resolution,[],[f387,f257])).

fof(f387,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | k1_funct_1(sK1,sK2) = sK3
    | k2_funct_1(sK0) != sK1
    | ~ spl15_26 ),
    inference(subsumption_resolution,[],[f88,f263])).

fof(f88,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | k1_funct_1(sK1,sK2) = sK3
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f380,plain,
    ( spl15_46
    | spl15_48
    | ~ spl15_24
    | ~ spl15_26 ),
    inference(avatar_split_clause,[],[f367,f262,f256,f378,f372])).

fof(f367,plain,
    ( r2_hidden(sK2,k1_relat_1(sK1))
    | r2_hidden(sK3,k1_relat_1(sK0))
    | ~ spl15_24
    | ~ spl15_26 ),
    inference(forward_demodulation,[],[f366,f263])).

fof(f366,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | r2_hidden(sK2,k2_relat_1(sK0))
    | ~ spl15_24
    | ~ spl15_26 ),
    inference(subsumption_resolution,[],[f365,f257])).

fof(f365,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | r2_hidden(sK2,k2_relat_1(sK0))
    | k2_funct_1(sK0) != sK1
    | ~ spl15_26 ),
    inference(subsumption_resolution,[],[f87,f263])).

fof(f87,plain,
    ( r2_hidden(sK3,k1_relat_1(sK0))
    | r2_hidden(sK2,k2_relat_1(sK0))
    | k1_relat_1(sK1) != k2_relat_1(sK0)
    | k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f356,plain,
    ( spl15_44
    | ~ spl15_22
    | ~ spl15_40 ),
    inference(avatar_split_clause,[],[f348,f335,f249,f354])).

fof(f249,plain,
    ( spl15_22
  <=> k1_relat_1(k4_relat_1(sK1)) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).

fof(f348,plain,
    ( k1_relat_1(sK0) = k2_relat_1(sK1)
    | ~ spl15_22
    | ~ spl15_40 ),
    inference(forward_demodulation,[],[f250,f336])).

fof(f250,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k2_relat_1(sK1)
    | ~ spl15_22 ),
    inference(avatar_component_clause,[],[f249])).

fof(f344,plain,
    ( spl15_42
    | ~ spl15_24
    | ~ spl15_32 ),
    inference(avatar_split_clause,[],[f327,f287,f256,f342])).

fof(f327,plain,
    ( k4_relat_1(sK0) = sK1
    | ~ spl15_24
    | ~ spl15_32 ),
    inference(backward_demodulation,[],[f257,f288])).

fof(f337,plain,
    ( spl15_40
    | ~ spl15_24
    | ~ spl15_34 ),
    inference(avatar_split_clause,[],[f325,f295,f256,f335])).

fof(f325,plain,
    ( k4_relat_1(sK1) = sK0
    | ~ spl15_24
    | ~ spl15_34 ),
    inference(backward_demodulation,[],[f257,f296])).

fof(f324,plain,
    ( spl15_24
    | spl15_38
    | ~ spl15_26 ),
    inference(avatar_split_clause,[],[f316,f262,f322,f256])).

fof(f316,plain,
    ( ! [X5] :
        ( r2_hidden(k1_funct_1(sK0,X5),k1_relat_1(sK1))
        | ~ r2_hidden(X5,k1_relat_1(sK0))
        | k2_funct_1(sK0) = sK1 )
    | ~ spl15_26 ),
    inference(forward_demodulation,[],[f132,f263])).

fof(f132,plain,(
    ! [X5] :
      ( r2_hidden(k1_funct_1(sK0,X5),k2_relat_1(sK0))
      | ~ r2_hidden(X5,k1_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,k2_relat_1(sK0))
      | k1_funct_1(sK0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(sK0))
      | k2_funct_1(sK0) = sK1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f312,plain,
    ( spl15_36
    | ~ spl15_0
    | ~ spl15_32 ),
    inference(avatar_split_clause,[],[f299,f287,f152,f310])).

fof(f299,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl15_0
    | ~ spl15_32 ),
    inference(subsumption_resolution,[],[f298,f153])).

fof(f298,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl15_32 ),
    inference(superposition,[],[f98,f288])).

fof(f297,plain,
    ( spl15_34
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_16 ),
    inference(avatar_split_clause,[],[f282,f215,f166,f159,f152,f295])).

fof(f166,plain,
    ( spl15_4
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f215,plain,
    ( spl15_16
  <=> k4_relat_1(k4_relat_1(sK0)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f282,plain,
    ( k4_relat_1(k2_funct_1(sK0)) = sK0
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_16 ),
    inference(backward_demodulation,[],[f281,f216])).

fof(f216,plain,
    ( k4_relat_1(k4_relat_1(sK0)) = sK0
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f215])).

fof(f281,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f280,f153])).

fof(f280,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f279,f160])).

fof(f279,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl15_4 ),
    inference(resolution,[],[f112,f167])).

fof(f167,plain,
    ( v2_funct_1(sK0)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f166])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t54_funct_1.p',d9_funct_1)).

fof(f289,plain,
    ( spl15_32
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f281,f166,f159,f152,f287])).

fof(f278,plain,
    ( spl15_30
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f235,f173,f276])).

fof(f276,plain,
    ( spl15_30
  <=> k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_30])])).

fof(f235,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1))
    | ~ spl15_6 ),
    inference(resolution,[],[f101,f174])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t54_funct_1.p',t37_relat_1)).

fof(f271,plain,
    ( spl15_28
    | ~ spl15_0 ),
    inference(avatar_split_clause,[],[f234,f152,f269])).

fof(f234,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl15_0 ),
    inference(resolution,[],[f101,f153])).

fof(f264,plain,
    ( spl15_24
    | spl15_26 ),
    inference(avatar_split_clause,[],[f82,f262,f256])).

fof(f82,plain,
    ( k1_relat_1(sK1) = k2_relat_1(sK0)
    | k2_funct_1(sK0) = sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f251,plain,
    ( spl15_22
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f230,f173,f249])).

fof(f230,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k2_relat_1(sK1)
    | ~ spl15_6 ),
    inference(resolution,[],[f100,f174])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f242,plain,
    ( spl15_20
    | ~ spl15_0 ),
    inference(avatar_split_clause,[],[f229,f152,f240])).

fof(f229,plain,
    ( k1_relat_1(k4_relat_1(sK0)) = k2_relat_1(sK0)
    | ~ spl15_0 ),
    inference(resolution,[],[f100,f153])).

fof(f217,plain,
    ( spl15_16
    | ~ spl15_0 ),
    inference(avatar_split_clause,[],[f207,f152,f215])).

fof(f207,plain,
    ( k4_relat_1(k4_relat_1(sK0)) = sK0
    | ~ spl15_0 ),
    inference(resolution,[],[f99,f153])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t54_funct_1.p',involutiveness_k4_relat_1)).

fof(f182,plain,(
    spl15_8 ),
    inference(avatar_split_clause,[],[f81,f180])).

fof(f81,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f175,plain,(
    spl15_6 ),
    inference(avatar_split_clause,[],[f80,f173])).

fof(f80,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f168,plain,(
    spl15_4 ),
    inference(avatar_split_clause,[],[f79,f166])).

fof(f79,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f161,plain,(
    spl15_2 ),
    inference(avatar_split_clause,[],[f78,f159])).

fof(f78,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f154,plain,(
    spl15_0 ),
    inference(avatar_split_clause,[],[f77,f152])).

fof(f77,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
