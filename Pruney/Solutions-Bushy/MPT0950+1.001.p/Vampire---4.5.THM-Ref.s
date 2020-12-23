%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0950+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:57 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  156 (1299 expanded)
%              Number of leaves         :   25 ( 295 expanded)
%              Depth                    :   42
%              Number of atoms          :  691 (6041 expanded)
%              Number of equality atoms :   50 ( 576 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f136,f153,f1278,f1319])).

fof(f1319,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f1313])).

fof(f1313,plain,
    ( $false
    | ~ spl5_1 ),
    inference(resolution,[],[f104,f60])).

fof(f60,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK0)),sK1)
    & r1_tarski(sK0,sK1)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f48])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK0)),sK1)
      & r1_tarski(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ( r1_tarski(X0,X1)
         => r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r1_tarski(X0,X1)
       => r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord2)).

fof(f104,plain,
    ( ! [X1] : ~ v3_ordinal1(X1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_1
  <=> ! [X1] : ~ v3_ordinal1(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1278,plain,
    ( ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f1277])).

fof(f1277,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f1276,f1275])).

fof(f1275,plain,
    ( r1_ordinal1(sK1,sK1)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f135,f1270])).

fof(f1270,plain,
    ( sK1 = k2_wellord2(k1_wellord2(sK0))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1269,f61])).

fof(f61,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f1269,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK1 = k2_wellord2(k1_wellord2(sK0))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1263,f60])).

fof(f1263,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | sK1 = k2_wellord2(k1_wellord2(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f1163,f62])).

fof(f62,plain,(
    ~ r1_ordinal1(k2_wellord2(k1_wellord2(sK0)),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f1163,plain,
    ( ! [X0,X1] :
        ( r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
        | ~ v3_ordinal1(X1)
        | ~ r1_tarski(X0,X1)
        | k2_wellord2(k1_wellord2(X0)) = X1 )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1162,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v2_wellord1(k1_wellord2(X1))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_wellord1(k1_wellord2(X1))
          | ~ r1_tarski(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( r1_tarski(X1,X0)
         => v2_wellord1(k1_wellord2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord2)).

fof(f1162,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v3_ordinal1(X1)
        | r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
        | k2_wellord2(k1_wellord2(X0)) = X1
        | ~ v2_wellord1(k1_wellord2(X0)) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1161,f63])).

fof(f63,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f1161,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v3_ordinal1(X1)
        | r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
        | k2_wellord2(k1_wellord2(X0)) = X1
        | ~ v2_wellord1(k1_wellord2(X0))
        | ~ v1_relat_1(k1_wellord2(X0)) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f1159])).

fof(f1159,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v3_ordinal1(X1)
        | r1_ordinal1(k2_wellord2(k1_wellord2(X0)),X1)
        | k2_wellord2(k1_wellord2(X0)) = X1
        | ~ v3_ordinal1(X1)
        | ~ v2_wellord1(k1_wellord2(X0))
        | ~ v1_relat_1(k1_wellord2(X0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f1067,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k1_wellord2(X1))
      | k2_wellord2(X0) = X1
      | ~ v3_ordinal1(X1)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_wellord2(X0) = X1
              | ~ r4_wellord1(X0,k1_wellord2(X1)) )
            & ( r4_wellord1(X0,k1_wellord2(X1))
              | k2_wellord2(X0) != X1 ) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_wellord2(X0) = X1
          <=> r4_wellord1(X0,k1_wellord2(X1)) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_wellord2(X0) = X1
          <=> r4_wellord1(X0,k1_wellord2(X1)) )
          | ~ v3_ordinal1(X1) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( k2_wellord2(X0) = X1
            <=> r4_wellord1(X0,k1_wellord2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_wellord2)).

fof(f1067,plain,
    ( ! [X2,X3] :
        ( r4_wellord1(k1_wellord2(X2),k1_wellord2(X3))
        | ~ r1_tarski(X2,X3)
        | ~ v3_ordinal1(X3)
        | r1_ordinal1(k2_wellord2(k1_wellord2(X2)),X3) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1066,f63])).

fof(f1066,plain,
    ( ! [X2,X3] :
        ( r1_ordinal1(k2_wellord2(k1_wellord2(X2)),X3)
        | ~ r1_tarski(X2,X3)
        | ~ v3_ordinal1(X3)
        | r4_wellord1(k1_wellord2(X2),k1_wellord2(X3))
        | ~ v1_relat_1(k1_wellord2(X3)) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1063,f63])).

fof(f1063,plain,
    ( ! [X2,X3] :
        ( r1_ordinal1(k2_wellord2(k1_wellord2(X2)),X3)
        | ~ r1_tarski(X2,X3)
        | ~ v3_ordinal1(X3)
        | r4_wellord1(k1_wellord2(X2),k1_wellord2(X3))
        | ~ v1_relat_1(k1_wellord2(X2))
        | ~ v1_relat_1(k1_wellord2(X3)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f949,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f949,plain,
    ( ! [X57,X58] :
        ( r4_wellord1(k1_wellord2(X58),k1_wellord2(X57))
        | r1_ordinal1(k2_wellord2(k1_wellord2(X57)),X58)
        | ~ r1_tarski(X57,X58)
        | ~ v3_ordinal1(X58) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f892])).

fof(f892,plain,
    ( ! [X57,X58] :
        ( r1_ordinal1(k2_wellord2(k1_wellord2(X57)),X58)
        | r4_wellord1(k1_wellord2(X58),k1_wellord2(X57))
        | ~ r1_tarski(X57,X58)
        | ~ v3_ordinal1(X58)
        | ~ v3_ordinal1(X58)
        | ~ r1_tarski(X57,X58)
        | r4_wellord1(k1_wellord2(X58),k1_wellord2(X57)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f535,f853])).

fof(f853,plain,
    ( ! [X0,X1] :
        ( sK4(X1,k1_wellord2(X0)) = k2_wellord2(k1_wellord2(X1))
        | ~ v3_ordinal1(X0)
        | ~ r1_tarski(X1,X0)
        | r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f852,f71])).

fof(f852,plain,
    ( ! [X0,X1] :
        ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
        | ~ v3_ordinal1(X0)
        | ~ r1_tarski(X1,X0)
        | sK4(X1,k1_wellord2(X0)) = k2_wellord2(k1_wellord2(X1))
        | ~ v2_wellord1(k1_wellord2(X1)) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f851,f467])).

fof(f467,plain,
    ( ! [X0,X1] :
        ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
        | ~ r1_tarski(X0,X1)
        | ~ v3_ordinal1(X1)
        | v3_ordinal1(sK4(X0,k1_wellord2(X1))) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f464])).

fof(f464,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
        | ~ v3_ordinal1(X1)
        | v3_ordinal1(sK4(X0,k1_wellord2(X1)))
        | ~ v3_ordinal1(X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f356,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_ordinal1(X1)
          | ~ m1_subset_1(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_ordinal1)).

fof(f356,plain,
    ( ! [X4,X3] :
        ( m1_subset_1(sK4(X4,k1_wellord2(X3)),X3)
        | ~ r1_tarski(X4,X3)
        | r4_wellord1(k1_wellord2(X3),k1_wellord2(X4))
        | ~ v3_ordinal1(X3) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f351,f205])).

fof(f205,plain,
    ( ! [X2] :
        ( v2_wellord1(k1_wellord2(X2))
        | ~ v3_ordinal1(X2) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | v2_wellord1(k1_wellord2(X2))
        | ~ v3_ordinal1(X2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f140,f71])).

fof(f140,plain,
    ( ! [X0] :
        ( r1_tarski(X0,X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( ! [X0] :
        ( r1_tarski(X0,X0)
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f85,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( r1_ordinal1(X0,X0)
        | ~ v3_ordinal1(X0) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_2
  <=> ! [X0] :
        ( r1_ordinal1(X0,X0)
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f351,plain,
    ( ! [X4,X3] :
        ( r4_wellord1(k1_wellord2(X3),k1_wellord2(X4))
        | ~ v2_wellord1(k1_wellord2(X3))
        | ~ r1_tarski(X4,X3)
        | m1_subset_1(sK4(X4,k1_wellord2(X3)),X3)
        | ~ v3_ordinal1(X3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f263,f215])).

fof(f215,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | m1_subset_1(X2,X3)
        | ~ v3_ordinal1(X3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f148,f140])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f89,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f263,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1,k1_wellord2(X0)),X0)
      | r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f262])).

fof(f262,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | r2_hidden(sK4(X1,k1_wellord2(X0)),X0)
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f176,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f176,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | r2_hidden(sK4(X1,k1_wellord2(X0)),X0)
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f175,f63])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1,k1_wellord2(X0)),X0)
      | r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ r1_tarski(X1,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f80,f101])).

fof(f101,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f97,f63])).

fof(f97,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_relat_1(X1))
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK4(X0,X1))),k2_wellord1(X1,X0))
        & r2_hidden(sK4(X0,X1),k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
     => ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK4(X0,X1))),k2_wellord1(X1,X0))
        & r2_hidden(sK4(X0,X1),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
          & r2_hidden(X2,k3_relat_1(X1)) )
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] :
              ~ ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X2)),k2_wellord1(X1,X0))
                & r2_hidden(X2,k3_relat_1(X1)) )
          & ~ r4_wellord1(X1,k2_wellord1(X1,X0))
          & v2_wellord1(X1)
          & r1_tarski(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_wellord1)).

fof(f851,plain,
    ( ! [X0,X1] :
        ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
        | ~ v3_ordinal1(X0)
        | ~ r1_tarski(X1,X0)
        | sK4(X1,k1_wellord2(X0)) = k2_wellord2(k1_wellord2(X1))
        | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0)))
        | ~ v2_wellord1(k1_wellord2(X1)) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f849,f63])).

fof(f849,plain,
    ( ! [X0,X1] :
        ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
        | ~ v3_ordinal1(X0)
        | ~ r1_tarski(X1,X0)
        | sK4(X1,k1_wellord2(X0)) = k2_wellord2(k1_wellord2(X1))
        | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0)))
        | ~ v2_wellord1(k1_wellord2(X1))
        | ~ v1_relat_1(k1_wellord2(X1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f707,f66])).

fof(f707,plain,
    ( ! [X2,X3] :
        ( r4_wellord1(k1_wellord2(X2),k1_wellord2(sK4(X2,k1_wellord2(X3))))
        | r4_wellord1(k1_wellord2(X3),k1_wellord2(X2))
        | ~ v3_ordinal1(X3)
        | ~ r1_tarski(X2,X3) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f706,f631])).

fof(f631,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK4(X1,k1_wellord2(X0)),X0)
        | ~ r1_tarski(X1,X0)
        | ~ v3_ordinal1(X0)
        | r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f630,f467])).

fof(f630,plain,
    ( ! [X0,X1] :
        ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
        | ~ r1_tarski(X1,X0)
        | ~ v3_ordinal1(X0)
        | r1_tarski(sK4(X1,k1_wellord2(X0)),X0)
        | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0))) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f629])).

fof(f629,plain,
    ( ! [X0,X1] :
        ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
        | ~ r1_tarski(X1,X0)
        | ~ v3_ordinal1(X0)
        | r1_tarski(sK4(X1,k1_wellord2(X0)),X0)
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f535,f85])).

fof(f706,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | r4_wellord1(k1_wellord2(X3),k1_wellord2(X2))
        | ~ v3_ordinal1(X3)
        | ~ r1_tarski(sK4(X2,k1_wellord2(X3)),X3)
        | r4_wellord1(k1_wellord2(X2),k1_wellord2(sK4(X2,k1_wellord2(X3)))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f705,f467])).

fof(f705,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | r4_wellord1(k1_wellord2(X3),k1_wellord2(X2))
        | ~ v3_ordinal1(X3)
        | ~ v3_ordinal1(sK4(X2,k1_wellord2(X3)))
        | ~ r1_tarski(sK4(X2,k1_wellord2(X3)),X3)
        | r4_wellord1(k1_wellord2(X2),k1_wellord2(sK4(X2,k1_wellord2(X3)))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f704,f63])).

fof(f704,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | r4_wellord1(k1_wellord2(X3),k1_wellord2(X2))
        | ~ v3_ordinal1(X3)
        | ~ v3_ordinal1(sK4(X2,k1_wellord2(X3)))
        | ~ r1_tarski(sK4(X2,k1_wellord2(X3)),X3)
        | r4_wellord1(k1_wellord2(X2),k1_wellord2(sK4(X2,k1_wellord2(X3))))
        | ~ v1_relat_1(k1_wellord2(sK4(X2,k1_wellord2(X3)))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f699,f63])).

fof(f699,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | r4_wellord1(k1_wellord2(X3),k1_wellord2(X2))
        | ~ v3_ordinal1(X3)
        | ~ v3_ordinal1(sK4(X2,k1_wellord2(X3)))
        | ~ r1_tarski(sK4(X2,k1_wellord2(X3)),X3)
        | r4_wellord1(k1_wellord2(X2),k1_wellord2(sK4(X2,k1_wellord2(X3))))
        | ~ v1_relat_1(k1_wellord2(X2))
        | ~ v1_relat_1(k1_wellord2(sK4(X2,k1_wellord2(X3)))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f433,f67])).

fof(f433,plain,
    ( ! [X0,X1] :
        ( r4_wellord1(k1_wellord2(sK4(X1,k1_wellord2(X0))),k1_wellord2(X1))
        | ~ r1_tarski(X1,X0)
        | r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0)))
        | ~ r1_tarski(sK4(X1,k1_wellord2(X0)),X0) )
    | ~ spl5_2 ),
    inference(superposition,[],[f306,f82])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( r4_wellord1(k2_wellord1(k1_wellord2(X0),sK4(X1,k1_wellord2(X0))),k1_wellord2(X1))
        | ~ r1_tarski(X1,X0)
        | r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f303,f205])).

fof(f303,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k2_wellord1(k1_wellord2(X0),sK4(X1,k1_wellord2(X0))),k1_wellord2(X1))
      | ~ r1_tarski(X1,X0)
      | r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0))) ) ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k2_wellord1(k1_wellord2(X0),sK4(X1,k1_wellord2(X0))),k1_wellord2(X1))
      | ~ r1_tarski(X1,X0)
      | r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0)))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f183,f82])).

fof(f183,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k2_wellord1(k1_wellord2(X0),sK4(X1,k1_wellord2(X0))),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r1_tarski(X1,X0)
      | r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0))) ) ),
    inference(subsumption_resolution,[],[f182,f176])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r4_wellord1(k2_wellord1(k1_wellord2(X0),sK4(X1,k1_wellord2(X0))),k2_wellord1(k1_wellord2(X0),X1))
      | r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ r2_hidden(sK4(X1,k1_wellord2(X0)),X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0))) ) ),
    inference(forward_demodulation,[],[f181,f101])).

fof(f181,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k2_wellord1(k1_wellord2(X0),sK4(X1,k1_wellord2(X0))),k2_wellord1(k1_wellord2(X0),X1))
      | r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ r1_tarski(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r2_hidden(sK4(X1,k1_wellord2(X0)),X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0))) ) ),
    inference(subsumption_resolution,[],[f178,f63])).

fof(f178,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k2_wellord1(k1_wellord2(X0),sK4(X1,k1_wellord2(X0))),k2_wellord1(k1_wellord2(X0),X1))
      | r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ r1_tarski(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(sK4(X1,k1_wellord2(X0)),X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(sK4(X1,k1_wellord2(X0))) ) ),
    inference(superposition,[],[f81,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f81,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,sK4(X0,X1))),k2_wellord1(X1,X0))
      | r4_wellord1(X1,k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f535,plain,
    ( ! [X4,X3] :
        ( r1_ordinal1(sK4(X4,k1_wellord2(X3)),X3)
        | r4_wellord1(k1_wellord2(X3),k1_wellord2(X4))
        | ~ r1_tarski(X4,X3)
        | ~ v3_ordinal1(X3) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f534,f467])).

fof(f534,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X4,X3)
        | r4_wellord1(k1_wellord2(X3),k1_wellord2(X4))
        | r1_ordinal1(sK4(X4,k1_wellord2(X3)),X3)
        | ~ v3_ordinal1(X3)
        | ~ v3_ordinal1(sK4(X4,k1_wellord2(X3))) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f533,f205])).

fof(f533,plain,(
    ! [X4,X3] :
      ( ~ v2_wellord1(k1_wellord2(X3))
      | ~ r1_tarski(X4,X3)
      | r4_wellord1(k1_wellord2(X3),k1_wellord2(X4))
      | r1_ordinal1(sK4(X4,k1_wellord2(X3)),X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(sK4(X4,k1_wellord2(X3))) ) ),
    inference(subsumption_resolution,[],[f530,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f530,plain,(
    ! [X4,X3] :
      ( ~ v2_wellord1(k1_wellord2(X3))
      | ~ r1_tarski(X4,X3)
      | r4_wellord1(k1_wellord2(X3),k1_wellord2(X4))
      | ~ v1_ordinal1(X3)
      | r1_ordinal1(sK4(X4,k1_wellord2(X3)),X3)
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(sK4(X4,k1_wellord2(X3))) ) ),
    inference(resolution,[],[f352,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f352,plain,(
    ! [X6,X5] :
      ( r1_tarski(sK4(X6,k1_wellord2(X5)),X5)
      | ~ v2_wellord1(k1_wellord2(X5))
      | ~ r1_tarski(X6,X5)
      | r4_wellord1(k1_wellord2(X5),k1_wellord2(X6))
      | ~ v1_ordinal1(X5) ) ),
    inference(resolution,[],[f263,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f135,plain,
    ( r1_ordinal1(sK1,k2_wellord2(k1_wellord2(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_6
  <=> r1_ordinal1(sK1,k2_wellord2(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1276,plain,
    ( ~ r1_ordinal1(sK1,sK1)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f62,f1270])).

fof(f153,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f151,f63])).

fof(f151,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_5 ),
    inference(resolution,[],[f132,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_wellord2(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_wellord2(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v3_ordinal1(k2_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord2)).

fof(f132,plain,
    ( ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_5
  <=> v3_ordinal1(k2_wellord2(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f136,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f129,f134,f131])).

fof(f129,plain,
    ( r1_ordinal1(sK1,k2_wellord2(k1_wellord2(sK0)))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0))) ),
    inference(subsumption_resolution,[],[f126,f60])).

fof(f126,plain,
    ( r1_ordinal1(sK1,k2_wellord2(k1_wellord2(sK0)))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2(sK0)))
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f84,f62])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f108,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f83,f106,f103])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).

%------------------------------------------------------------------------------
