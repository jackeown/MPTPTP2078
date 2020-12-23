%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1216+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:29 EST 2020

% Result     : Theorem 3.16s
% Output     : Refutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  223 (5862 expanded)
%              Number of leaves         :   31 (1968 expanded)
%              Depth                    :   20
%              Number of atoms          :  877 (51081 expanded)
%              Number of equality atoms :  165 (10061 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6395,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f152,f153,f3258,f6392])).

fof(f6392,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f6391])).

fof(f6391,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f6390,f147])).

fof(f147,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl8_1
  <=> k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f6390,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f5285,f5656])).

fof(f5656,plain,
    ( k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f5525,f3306])).

fof(f3306,plain,
    ( k5_lattices(sK0) = k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f3293,f561])).

fof(f561,plain,(
    k5_lattices(sK0) = k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) ),
    inference(backward_demodulation,[],[f530,f559])).

fof(f559,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) ),
    inference(forward_demodulation,[],[f522,f167])).

fof(f167,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f94,f95,f96,f97,f99,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattices)).

fof(f99,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,
    ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
      | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2) )
    & ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
      | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f76,f79,f78,f77])).

fof(f77,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
                & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(sK0,X1,k7_lattices(sK0,X2))
                | k4_lattices(sK0,X1,X2) != k5_lattices(sK0) )
              & ( r3_lattices(sK0,X1,k7_lattices(sK0,X2))
                | k4_lattices(sK0,X1,X2) = k5_lattices(sK0) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r3_lattices(sK0,X1,k7_lattices(sK0,X2))
              | k4_lattices(sK0,X1,X2) != k5_lattices(sK0) )
            & ( r3_lattices(sK0,X1,k7_lattices(sK0,X2))
              | k4_lattices(sK0,X1,X2) = k5_lattices(sK0) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
            | k5_lattices(sK0) != k4_lattices(sK0,sK1,X2) )
          & ( r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
            | k5_lattices(sK0) = k4_lattices(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
    ( ? [X2] :
        ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
          | k5_lattices(sK0) != k4_lattices(sK0,sK1,X2) )
        & ( r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
          | k5_lattices(sK0) = k4_lattices(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
        | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2) )
      & ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
        | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
              & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
              & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_lattices)).

fof(f97,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f96,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f95,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f94,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f522,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f99,f168,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f168,plain,(
    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f94,f97,f99,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f154,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f97,f102])).

fof(f102,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f159,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f94,f95,f97,f112])).

fof(f112,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f530,plain,(
    k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f99,f168,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f3293,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f683,f3284])).

fof(f3284,plain,
    ( k7_lattices(sK0,sK2) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f504,f3262])).

fof(f3262,plain,
    ( k7_lattices(sK0,sK2) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f94,f155,f98,f168,f3259,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(f3259,plain,
    ( r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f94,f159,f161,f162,f97,f98,f168,f150,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f150,plain,
    ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl8_2
  <=> r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f162,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f94,f95,f97,f115])).

fof(f115,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f161,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f94,f95,f97,f114])).

fof(f114,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f80])).

fof(f155,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f97,f103])).

fof(f103,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f504,plain,(
    k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f158,f155,f98,f168,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f158,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f94,f95,f97,f111])).

fof(f111,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f683,plain,(
    k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    inference(forward_demodulation,[],[f682,f583])).

fof(f583,plain,(
    k1_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(backward_demodulation,[],[f500,f496])).

fof(f496,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f158,f155,f98,f168,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f500,plain,(
    k1_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f94,f158,f155,f98,f168,f136])).

fof(f682,plain,(
    k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK2,k1_lattices(sK0,k7_lattices(sK0,sK2),sK1)) ),
    inference(forward_demodulation,[],[f681,f561])).

fof(f681,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f452,f225])).

fof(f225,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f210,f214])).

fof(f214,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f94,f154,f98,f99,f159,f140])).

fof(f210,plain,(
    k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f94,f154,f98,f99,f159,f141])).

fof(f452,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k2_lattices(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f94,f97,f156,f99,f98,f168,f125])).

fof(f125,plain,(
    ! [X6,X4,X0,X5] :
      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k2_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),sK5(X0))) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),k2_lattices(X0,sK3(X0),sK5(X0)))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f83,f86,f85,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k2_lattices(X0,sK3(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),k2_lattices(X0,sK3(X0),X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,sK3(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),k2_lattices(X0,sK3(X0),X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),k2_lattices(X0,sK3(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),k2_lattices(X0,sK3(X0),X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK3(X0),k1_lattices(X0,sK4(X0),sK5(X0))) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),k2_lattices(X0,sK3(X0),sK5(X0)))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattices)).

fof(f156,plain,(
    v11_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f94,f96,f97,f108])).

fof(f108,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

fof(f5525,plain,(
    k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f158,f155,f330,f217,f136])).

fof(f217,plain,(
    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f94,f154,f99,f98,f159,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f330,plain,(
    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f313,f329])).

fof(f329,plain,(
    k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f307,f164])).

fof(f164,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f94,f95,f96,f97,f98,f124])).

fof(f307,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f98,f165,f141])).

fof(f165,plain,(
    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f94,f97,f98,f134])).

fof(f313,plain,(
    m1_subset_1(k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f94,f154,f98,f165,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f5285,plain,(
    k4_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f95,f185,f97,f217,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k5_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

fof(f185,plain,(
    v13_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f97,f94,f157,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_lattices)).

fof(f157,plain,(
    v15_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f94,f96,f97,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3258,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f3257])).

fof(f3257,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f3256,f3088])).

fof(f3088,plain,
    ( k7_lattices(sK0,sK2) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f2445,f3080])).

fof(f3080,plain,
    ( sK1 = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f2369,f2976])).

fof(f2976,plain,
    ( sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f1532,f146])).

fof(f146,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f145])).

fof(f1532,plain,(
    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f1493,f1529])).

fof(f1529,plain,(
    sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1448,f761])).

fof(f761,plain,(
    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f94,f95,f97,f98,f186,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

fof(f186,plain,(
    v14_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f97,f94,f157,f106])).

fof(f106,plain,(
    ! [X0] :
      ( v14_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1448,plain,(
    k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f98,f345,f140])).

fof(f345,plain,(
    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f319,f344])).

fof(f344,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f289,f163])).

fof(f163,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f94,f95,f96,f97,f98,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattices)).

fof(f289,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f94,f158,f155,f98,f165,f136])).

fof(f319,plain,(
    m1_subset_1(k1_lattices(sK0,k7_lattices(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f94,f155,f98,f165,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattices)).

fof(f1493,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f672,f1460])).

fof(f1460,plain,(
    k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f98,f345,f141])).

fof(f672,plain,(
    k2_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f671,f574])).

fof(f574,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(forward_demodulation,[],[f501,f166])).

fof(f166,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f94,f95,f96,f97,f99,f123])).

fof(f501,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k1_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f94,f158,f155,f99,f168,f136])).

fof(f671,plain,(
    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f670,f529])).

fof(f529,plain,(
    k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f98,f168,f141])).

fof(f670,plain,(
    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f455,f209])).

fof(f209,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f94,f154,f99,f98,f159,f141])).

fof(f455,plain,(
    k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k2_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f97,f156,f98,f99,f168,f125])).

fof(f2369,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f634,f2323])).

fof(f2323,plain,(
    k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f168,f201,f141])).

fof(f201,plain,(
    m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f175,f198])).

fof(f198,plain,(
    k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f189,f193])).

fof(f193,plain,(
    k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f94,f155,f98,f99,f158,f135])).

fof(f189,plain,(
    k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f94,f155,f98,f99,f158,f136])).

fof(f175,plain,(
    m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f94,f98,f99,f155,f143])).

fof(f634,plain,(
    k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f633,f188])).

fof(f188,plain,(
    k1_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f94,f155,f99,f98,f158,f136])).

fof(f633,plain,(
    k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f632,f563])).

fof(f563,plain,(
    k2_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(backward_demodulation,[],[f525,f521])).

fof(f521,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f98,f168,f140])).

fof(f525,plain,(
    k2_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f98,f168,f141])).

fof(f632,plain,(
    k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),sK1),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f468,f554])).

fof(f554,plain,(
    k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(forward_demodulation,[],[f526,f167])).

fof(f526,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f99,f168,f141])).

fof(f468,plain,(
    k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),sK1),k2_lattices(sK0,k7_lattices(sK0,sK2),sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f97,f156,f99,f98,f168,f125])).

fof(f2445,plain,(
    k7_lattices(sK0,sK2) = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)),k7_lattices(sK0,sK2)) ),
    inference(forward_demodulation,[],[f2245,f2392])).

fof(f2392,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f2316,f2309])).

fof(f2309,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f168,f201,f140])).

fof(f2316,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f159,f154,f168,f201,f141])).

fof(f2245,plain,(
    k7_lattices(sK0,sK2) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)),k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f94,f97,f161,f168,f201,f130])).

fof(f130,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK7(X0) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f89,f91,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK7(X0) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0))
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(f3256,plain,
    ( k7_lattices(sK0,sK2) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f94,f155,f98,f168,f3253,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f3253,plain,
    ( ~ r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f94,f159,f161,f162,f97,f98,f168,f151,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f151,plain,
    ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f149])).

fof(f153,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f100,f149,f145])).

fof(f100,plain,
    ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f80])).

fof(f152,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f101,f149,f145])).

fof(f101,plain,
    ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f80])).

%------------------------------------------------------------------------------
