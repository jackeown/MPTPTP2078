%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1845+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:34 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   38 (  74 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :  111 ( 299 expanded)
%              Number of equality atoms :   12 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14708)lrs+4_1_acc=on:afr=on:afp=100000:afq=1.2:amm=sco:anc=none:bd=off:bs=on:bsr=on:ccuc=first:fsr=off:fde=unused:irw=on:lma=on:nm=0:nwc=1.3:stl=30:sd=10:ss=axioms:st=3.0:sos=all:sp=occurrence:uhcvi=on_26 on theBenchmark
fof(f6045,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5157,f5161,f5165,f5169,f5173,f5292,f6044])).

fof(f6044,plain,
    ( ~ spl162_2
    | ~ spl162_5
    | spl162_25 ),
    inference(avatar_split_clause,[],[f6043,f5290,f5171,f5159])).

fof(f5159,plain,
    ( spl162_2
  <=> v2_pre_topc(sK70) ),
    introduced(avatar_definition,[new_symbols(naming,[spl162_2])])).

fof(f5171,plain,
    ( spl162_5
  <=> l1_pre_topc(sK70) ),
    introduced(avatar_definition,[new_symbols(naming,[spl162_5])])).

fof(f5290,plain,
    ( spl162_25
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK70),u1_pre_topc(sK70))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl162_25])])).

fof(f6043,plain,
    ( ~ l1_pre_topc(sK70)
    | ~ v2_pre_topc(sK70)
    | spl162_25 ),
    inference(resolution,[],[f5291,f4484])).

fof(f4484,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3627])).

fof(f3627,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3626])).

fof(f3626,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1801])).

fof(f1801,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f5291,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK70),u1_pre_topc(sK70)))
    | spl162_25 ),
    inference(avatar_component_clause,[],[f5290])).

fof(f5292,plain,
    ( ~ spl162_4
    | spl162_1
    | ~ spl162_25
    | ~ spl162_3 ),
    inference(avatar_split_clause,[],[f5241,f5163,f5290,f5155,f5167])).

fof(f5167,plain,
    ( spl162_4
  <=> l1_pre_topc(sK71) ),
    introduced(avatar_definition,[new_symbols(naming,[spl162_4])])).

fof(f5155,plain,
    ( spl162_1
  <=> v2_pre_topc(sK71) ),
    introduced(avatar_definition,[new_symbols(naming,[spl162_1])])).

fof(f5163,plain,
    ( spl162_3
  <=> g1_pre_topc(u1_struct_0(sK70),u1_pre_topc(sK70)) = g1_pre_topc(u1_struct_0(sK71),u1_pre_topc(sK71)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl162_3])])).

fof(f5241,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK70),u1_pre_topc(sK70)))
    | v2_pre_topc(sK71)
    | ~ l1_pre_topc(sK71)
    | ~ spl162_3 ),
    inference(superposition,[],[f4499,f5164])).

fof(f5164,plain,
    ( g1_pre_topc(u1_struct_0(sK70),u1_pre_topc(sK70)) = g1_pre_topc(u1_struct_0(sK71),u1_pre_topc(sK71))
    | ~ spl162_3 ),
    inference(avatar_component_clause,[],[f5163])).

fof(f4499,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3644])).

fof(f3644,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3643])).

fof(f3643,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1849])).

fof(f1849,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_pre_topc)).

fof(f5173,plain,(
    spl162_5 ),
    inference(avatar_split_clause,[],[f4450,f5171])).

fof(f4450,plain,(
    l1_pre_topc(sK70) ),
    inference(cnf_transformation,[],[f4098])).

fof(f4098,plain,
    ( ~ v2_pre_topc(sK71)
    & v2_pre_topc(sK70)
    & g1_pre_topc(u1_struct_0(sK70),u1_pre_topc(sK70)) = g1_pre_topc(u1_struct_0(sK71),u1_pre_topc(sK71))
    & l1_pre_topc(sK71)
    & l1_pre_topc(sK70) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK70,sK71])],[f3611,f4097,f4096])).

fof(f4096,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_pre_topc(X1)
            & v2_pre_topc(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(sK70)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK70),u1_pre_topc(sK70))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK70) ) ),
    introduced(choice_axiom,[])).

fof(f4097,plain,
    ( ? [X1] :
        ( ~ v2_pre_topc(X1)
        & v2_pre_topc(sK70)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK70),u1_pre_topc(sK70))
        & l1_pre_topc(X1) )
   => ( ~ v2_pre_topc(sK71)
      & v2_pre_topc(sK70)
      & g1_pre_topc(u1_struct_0(sK70),u1_pre_topc(sK70)) = g1_pre_topc(u1_struct_0(sK71),u1_pre_topc(sK71))
      & l1_pre_topc(sK71) ) ),
    introduced(choice_axiom,[])).

fof(f3611,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3610])).

fof(f3610,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3593])).

fof(f3593,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_pre_topc(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_pre_topc(X1) ) ) ) ),
    inference(negated_conjecture,[],[f3592])).

fof(f3592,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_pre_topc(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).

fof(f5169,plain,(
    spl162_4 ),
    inference(avatar_split_clause,[],[f4451,f5167])).

fof(f4451,plain,(
    l1_pre_topc(sK71) ),
    inference(cnf_transformation,[],[f4098])).

fof(f5165,plain,(
    spl162_3 ),
    inference(avatar_split_clause,[],[f4452,f5163])).

fof(f4452,plain,(
    g1_pre_topc(u1_struct_0(sK70),u1_pre_topc(sK70)) = g1_pre_topc(u1_struct_0(sK71),u1_pre_topc(sK71)) ),
    inference(cnf_transformation,[],[f4098])).

fof(f5161,plain,(
    spl162_2 ),
    inference(avatar_split_clause,[],[f4453,f5159])).

fof(f4453,plain,(
    v2_pre_topc(sK70) ),
    inference(cnf_transformation,[],[f4098])).

fof(f5157,plain,(
    ~ spl162_1 ),
    inference(avatar_split_clause,[],[f4454,f5155])).

fof(f4454,plain,(
    ~ v2_pre_topc(sK71) ),
    inference(cnf_transformation,[],[f4098])).
%------------------------------------------------------------------------------
