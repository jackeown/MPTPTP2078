%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t21_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:04 EDT 2019

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  645 (3162 expanded)
%              Number of leaves         :   61 ( 916 expanded)
%              Depth                    :   56
%              Number of atoms          : 8313 (42600 expanded)
%              Number of equality atoms :  264 ( 798 expanded)
%              Maximal formula depth    :   33 (  12 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f248,f249,f250,f251,f252,f254,f255,f256,f257,f258,f259,f260,f261,f262,f263,f264,f265,f379,f440,f453,f466,f479,f492,f499,f512,f533,f537,f541,f545,f549,f868,f918,f1792,f5586,f5610,f6137,f6996,f7441,f7771,f7785,f7949,f8003,f8050,f8226,f8340,f8389])).

fof(f8389,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(avatar_contradiction_clause,[],[f8388])).

fof(f8388,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8387,f98])).

fof(f98,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
      | ~ v1_waybel_7(sK1,k7_lattice3(sK0))
      | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
      | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_waybel_7(sK1,sK0)
      | ~ v13_waybel_0(sK1,sK0)
      | ~ v2_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
        & v1_waybel_7(sK1,k7_lattice3(sK0))
        & v12_waybel_0(sK1,k7_lattice3(sK0))
        & v1_waybel_0(sK1,k7_lattice3(sK0))
        & ~ v1_xboole_0(sK1) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_waybel_7(sK1,sK0)
        & v13_waybel_0(sK1,sK0)
        & v2_waybel_0(sK1,sK0)
        & ~ v1_xboole_0(sK1) ) )
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f81,f83,f82])).

fof(f82,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              | ~ v1_waybel_7(X1,k7_lattice3(X0))
              | ~ v12_waybel_0(X1,k7_lattice3(X0))
              | ~ v1_waybel_0(X1,k7_lattice3(X0))
              | v1_xboole_0(X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_waybel_7(X1,X0)
              | ~ v13_waybel_0(X1,X0)
              | ~ v2_waybel_0(X1,X0)
              | v1_xboole_0(X1) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
                & v1_waybel_7(X1,k7_lattice3(X0))
                & v12_waybel_0(X1,k7_lattice3(X0))
                & v1_waybel_0(X1,k7_lattice3(X0))
                & ~ v1_xboole_0(X1) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_waybel_7(X1,X0)
                & v13_waybel_0(X1,X0)
                & v2_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) ) ) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
            | ~ v1_waybel_7(X1,k7_lattice3(sK0))
            | ~ v12_waybel_0(X1,k7_lattice3(sK0))
            | ~ v1_waybel_0(X1,k7_lattice3(sK0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v2_waybel_7(X1,sK0)
            | ~ v13_waybel_0(X1,sK0)
            | ~ v2_waybel_0(X1,sK0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
              & v1_waybel_7(X1,k7_lattice3(sK0))
              & v12_waybel_0(X1,k7_lattice3(sK0))
              & v1_waybel_0(X1,k7_lattice3(sK0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_waybel_7(X1,sK0)
              & v13_waybel_0(X1,sK0)
              & v2_waybel_0(X1,sK0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_7(X1,k7_lattice3(X0))
            | ~ v12_waybel_0(X1,k7_lattice3(X0))
            | ~ v1_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_waybel_7(X1,X0)
            | ~ v13_waybel_0(X1,X0)
            | ~ v2_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          | ~ v1_waybel_7(sK1,k7_lattice3(X0))
          | ~ v12_waybel_0(sK1,k7_lattice3(X0))
          | ~ v1_waybel_0(sK1,k7_lattice3(X0))
          | v1_xboole_0(sK1)
          | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v2_waybel_7(sK1,X0)
          | ~ v13_waybel_0(sK1,X0)
          | ~ v2_waybel_0(sK1,X0)
          | v1_xboole_0(sK1) )
        & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(sK1,k7_lattice3(X0))
            & v12_waybel_0(sK1,k7_lattice3(X0))
            & v1_waybel_0(sK1,k7_lattice3(X0))
            & ~ v1_xboole_0(sK1) )
          | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(sK1,X0)
            & v13_waybel_0(sK1,X0)
            & v2_waybel_0(sK1,X0)
            & ~ v1_xboole_0(sK1) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_7(X1,k7_lattice3(X0))
            | ~ v12_waybel_0(X1,k7_lattice3(X0))
            | ~ v1_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_waybel_7(X1,X0)
            | ~ v13_waybel_0(X1,X0)
            | ~ v2_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v1_waybel_7(X1,k7_lattice3(X0))
            | ~ v12_waybel_0(X1,k7_lattice3(X0))
            | ~ v1_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_waybel_7(X1,X0)
            | ~ v13_waybel_0(X1,X0)
            | ~ v2_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v1_waybel_7(X1,k7_lattice3(X0))
              & v12_waybel_0(X1,k7_lattice3(X0))
              & v1_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',t21_waybel_7)).

fof(f8387,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8386,f99])).

fof(f99,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f8386,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8385,f100])).

fof(f100,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f8385,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8384,f101])).

fof(f101,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f8384,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8383,f102])).

fof(f102,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f8383,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8382,f103])).

fof(f103,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f8382,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8381,f196])).

fof(f196,plain,
    ( v2_waybel_0(sK1,sK0)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl7_0
  <=> v2_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f8381,plain,
    ( ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8380,f202])).

fof(f202,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl7_2
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f8380,plain,
    ( ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8375,f864])).

fof(f864,plain,
    ( k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f863])).

fof(f863,plain,
    ( spl7_104
  <=> k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f8375,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(resolution,[],[f8374,f208])).

fof(f208,plain,
    ( v2_waybel_7(sK1,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl7_4
  <=> v2_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f8374,plain,
    ( ! [X0] :
        ( ~ v2_waybel_7(sK1,X0)
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8373,f7784])).

fof(f7784,plain,
    ( ! [X2] :
        ( ~ v2_lattice3(X2)
        | ~ v3_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v5_orders_2(X2)
        | ~ v1_lattice3(X2)
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) )
    | ~ spl7_640 ),
    inference(avatar_component_clause,[],[f7783])).

fof(f7783,plain,
    ( spl7_640
  <=> ! [X2] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ v3_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v5_orders_2(X2)
        | ~ v1_lattice3(X2)
        | ~ v2_lattice3(X2)
        | ~ l1_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_640])])).

fof(f8373,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8372,f864])).

fof(f8372,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8371,f861])).

fof(f861,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f860])).

fof(f860,plain,
    ( spl7_102
  <=> u1_struct_0(sK0) = u1_struct_0(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f8371,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8370,f3346])).

fof(f3346,plain,
    ( u1_orders_2(sK0) = u1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(trivial_inequality_removal,[],[f3340])).

fof(f3340,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != k7_lattice3(k7_lattice3(sK0))
    | u1_orders_2(sK0) = u1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(superposition,[],[f981,f864])).

fof(f981,plain,
    ( ! [X0,X1] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(X0,X1)
        | u1_orders_2(k7_lattice3(k7_lattice3(sK0))) = X1 )
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_102 ),
    inference(forward_demodulation,[],[f977,f924])).

fof(f924,plain,
    ( k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ spl7_30
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f921,f359])).

fof(f359,plain,
    ( l1_orders_2(k7_lattice3(sK0))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl7_30
  <=> l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f921,plain,
    ( k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl7_102 ),
    inference(superposition,[],[f329,f861])).

fof(f329,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f326,f137])).

fof(f137,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',dt_k7_lattice3)).

fof(f326,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
      | ~ l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f139,f136])).

fof(f136,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',abstractness_v1_orders_2)).

fof(f977,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | u1_orders_2(k7_lattice3(k7_lattice3(sK0))) = X1 )
    | ~ spl7_36
    | ~ spl7_102 ),
    inference(resolution,[],[f925,f182])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',free_g1_orders_2)).

fof(f925,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(k7_lattice3(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl7_36
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f922,f417])).

fof(f417,plain,
    ( l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl7_36
  <=> l1_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f922,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(k7_lattice3(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_102 ),
    inference(superposition,[],[f135,f861])).

fof(f135,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',dt_u1_orders_2)).

fof(f8370,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8369,f443])).

fof(f443,plain,
    ( v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl7_44
  <=> v3_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f8369,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8368,f456])).

fof(f456,plain,
    ( v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl7_48
  <=> v4_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f8368,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8367,f430])).

fof(f430,plain,
    ( v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f429])).

fof(f429,plain,
    ( spl7_40
  <=> v5_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f8367,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8366,f469])).

fof(f469,plain,
    ( v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl7_52
  <=> v1_lattice3(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f8366,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8365,f482])).

fof(f482,plain,
    ( v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f481])).

fof(f481,plain,
    ( spl7_56
  <=> v2_lattice3(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f8365,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8364,f417])).

fof(f8364,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8363,f192])).

fof(f192,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

fof(f8363,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(resolution,[],[f8361,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_7(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_7(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_7(X2,X1)
                & v13_waybel_0(X2,X1)
                & v2_waybel_0(X2,X1)
                & ~ v1_xboole_0(X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_waybel_7(X2,X0)
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1)
          | ~ v2_lattice3(X1)
          | ~ v1_lattice3(X1)
          | ~ v5_orders_2(X1)
          | ~ v4_orders_2(X1)
          | ~ v3_orders_2(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_7(X2,X1)
                & v13_waybel_0(X2,X1)
                & v2_waybel_0(X2,X1)
                & ~ v1_xboole_0(X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_waybel_7(X2,X0)
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1)
          | ~ v2_lattice3(X1)
          | ~ v1_lattice3(X1)
          | ~ v5_orders_2(X1)
          | ~ v4_orders_2(X1)
          | ~ v3_orders_2(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & v2_lattice3(X1)
            & v1_lattice3(X1)
            & v5_orders_2(X1)
            & v4_orders_2(X1)
            & v3_orders_2(X1) )
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v2_waybel_7(X2,X0)
                  & v13_waybel_0(X2,X0)
                  & v2_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_7(X2,X1)
                  & v13_waybel_0(X2,X1)
                  & v2_waybel_0(X2,X1)
                  & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',t19_waybel_7)).

fof(f8361,plain,
    ( ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_6
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8360,f214])).

fof(f214,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f8360,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8359,f861])).

fof(f8359,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8358,f452])).

fof(f452,plain,
    ( v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl7_46
  <=> v3_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f8358,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8357,f465])).

fof(f465,plain,
    ( v4_orders_2(k7_lattice3(sK0))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl7_50
  <=> v4_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f8357,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8356,f439])).

fof(f439,plain,
    ( v5_orders_2(k7_lattice3(sK0))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl7_42
  <=> v5_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f8356,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8355,f491])).

fof(f491,plain,
    ( v1_lattice3(k7_lattice3(sK0))
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f490])).

fof(f490,plain,
    ( spl7_58
  <=> v1_lattice3(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f8355,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8354,f478])).

fof(f478,plain,
    ( v2_lattice3(k7_lattice3(sK0))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl7_54
  <=> v2_lattice3(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f8354,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_15
    | ~ spl7_30
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8353,f359])).

fof(f8353,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_15
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8352,f192])).

fof(f8352,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_15
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8351,f5561])).

fof(f5561,plain,
    ( v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_508 ),
    inference(avatar_component_clause,[],[f5560])).

fof(f5560,plain,
    ( spl7_508
  <=> v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_508])])).

fof(f8351,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_15
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8350,f5567])).

fof(f5567,plain,
    ( v13_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_510 ),
    inference(avatar_component_clause,[],[f5566])).

fof(f5566,plain,
    ( spl7_510
  <=> v13_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_510])])).

fof(f8350,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_15 ),
    inference(resolution,[],[f241,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v2_waybel_7(X1,k7_lattice3(X0))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ v2_waybel_0(X1,k7_lattice3(X0))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',t20_waybel_7)).

fof(f241,plain,
    ( ~ v1_waybel_7(sK1,k7_lattice3(sK0))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl7_15
  <=> ~ v1_waybel_7(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f8340,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(avatar_contradiction_clause,[],[f8339])).

fof(f8339,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8338,f98])).

fof(f8338,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8337,f99])).

fof(f8337,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8336,f100])).

fof(f8336,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8335,f101])).

fof(f8335,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8334,f102])).

fof(f8334,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8333,f103])).

fof(f8333,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8332,f196])).

fof(f8332,plain,
    ( ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8331,f202])).

fof(f8331,plain,
    ( ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8326,f864])).

fof(f8326,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(resolution,[],[f8325,f208])).

fof(f8325,plain,
    ( ! [X0] :
        ( ~ v2_waybel_7(sK1,X0)
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8324,f7784])).

fof(f8324,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8323,f864])).

fof(f8323,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8322,f861])).

fof(f8322,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8321,f3346])).

fof(f8321,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8320,f443])).

fof(f8320,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8319,f456])).

fof(f8319,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8318,f430])).

fof(f8318,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8317,f469])).

fof(f8317,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8316,f482])).

fof(f8316,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8315,f417])).

fof(f8315,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8314,f192])).

fof(f8314,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(resolution,[],[f8285,f143])).

fof(f8285,plain,
    ( ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_6
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8284,f214])).

fof(f8284,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8283,f861])).

fof(f8283,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8282,f452])).

fof(f8282,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8281,f465])).

fof(f8281,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8280,f439])).

fof(f8280,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8279,f491])).

fof(f8279,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8278,f478])).

fof(f8278,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_13
    | ~ spl7_30
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8277,f359])).

fof(f8277,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_13
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8276,f192])).

fof(f8276,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_13
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8275,f5561])).

fof(f8275,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_13
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8274,f5567])).

fof(f8274,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_13 ),
    inference(resolution,[],[f235,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v2_waybel_7(X1,k7_lattice3(X0))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ v2_waybel_0(X1,k7_lattice3(X0))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f235,plain,
    ( ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl7_13
  <=> ~ v12_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f8226,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(avatar_contradiction_clause,[],[f8225])).

fof(f8225,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8224,f98])).

fof(f8224,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8223,f99])).

fof(f8223,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8222,f100])).

fof(f8222,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8221,f101])).

fof(f8221,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8220,f102])).

fof(f8220,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8219,f103])).

fof(f8219,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8218,f196])).

fof(f8218,plain,
    ( ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8217,f202])).

fof(f8217,plain,
    ( ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8212,f864])).

fof(f8212,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(resolution,[],[f8153,f208])).

fof(f8153,plain,
    ( ! [X0] :
        ( ~ v2_waybel_7(sK1,X0)
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8152,f7784])).

fof(f8152,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8151,f864])).

fof(f8151,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8150,f861])).

fof(f8150,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8149,f3346])).

fof(f8149,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8148,f443])).

fof(f8148,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8147,f456])).

fof(f8147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8146,f430])).

fof(f8146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8145,f469])).

fof(f8145,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8144,f482])).

fof(f8144,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8143,f417])).

fof(f8143,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8142,f192])).

fof(f8142,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(resolution,[],[f8140,f143])).

fof(f8140,plain,
    ( ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_6
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8139,f214])).

fof(f8139,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f8138,f861])).

fof(f8138,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8137,f452])).

fof(f8137,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8136,f465])).

fof(f8136,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8135,f439])).

fof(f8135,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8134,f491])).

fof(f8134,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8133,f478])).

fof(f8133,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8132,f359])).

fof(f8132,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_17
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8131,f192])).

fof(f8131,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_17
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8130,f5561])).

fof(f8130,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_17
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f8129,f5567])).

fof(f8129,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_17 ),
    inference(resolution,[],[f247,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v2_waybel_7(X1,k7_lattice3(X0))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ v2_waybel_0(X1,k7_lattice3(X0))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f247,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl7_17
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f8050,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | spl7_509
    | ~ spl7_640 ),
    inference(avatar_contradiction_clause,[],[f8049])).

fof(f8049,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8048,f98])).

fof(f8048,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8047,f99])).

fof(f8047,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8046,f100])).

fof(f8046,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8045,f101])).

fof(f8045,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8044,f102])).

fof(f8044,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8043,f103])).

fof(f8043,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8042,f196])).

fof(f8042,plain,
    ( ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8041,f202])).

fof(f8041,plain,
    ( ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8036,f864])).

fof(f8036,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509
    | ~ spl7_640 ),
    inference(resolution,[],[f8035,f208])).

fof(f8035,plain,
    ( ! [X0] :
        ( ~ v2_waybel_7(sK1,X0)
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8034,f7784])).

fof(f8034,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509 ),
    inference(forward_demodulation,[],[f8033,f864])).

fof(f8033,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509 ),
    inference(forward_demodulation,[],[f8032,f861])).

fof(f8032,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_509 ),
    inference(forward_demodulation,[],[f8031,f3346])).

fof(f8031,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f8030,f443])).

fof(f8030,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f8029,f456])).

fof(f8029,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f8028,f430])).

fof(f8028,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f8027,f469])).

fof(f8027,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_56
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f8026,f482])).

fof(f8026,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f8025,f417])).

fof(f8025,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f8024,f192])).

fof(f8024,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_509 ),
    inference(resolution,[],[f5564,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_7(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5564,plain,
    ( ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_509 ),
    inference(avatar_component_clause,[],[f5563])).

fof(f5563,plain,
    ( spl7_509
  <=> ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_509])])).

fof(f8003,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | spl7_511
    | ~ spl7_640 ),
    inference(avatar_contradiction_clause,[],[f8002])).

fof(f8002,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8001,f98])).

fof(f8001,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f8000,f99])).

fof(f8000,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7999,f100])).

fof(f7999,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7998,f101])).

fof(f7998,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7997,f102])).

fof(f7997,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7996,f103])).

fof(f7996,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7995,f196])).

fof(f7995,plain,
    ( ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7994,f202])).

fof(f7994,plain,
    ( ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7989,f864])).

fof(f7989,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511
    | ~ spl7_640 ),
    inference(resolution,[],[f7988,f208])).

fof(f7988,plain,
    ( ! [X0] :
        ( ~ v2_waybel_7(sK1,X0)
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7987,f7784])).

fof(f7987,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511 ),
    inference(forward_demodulation,[],[f7986,f864])).

fof(f7986,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511 ),
    inference(forward_demodulation,[],[f7985,f861])).

fof(f7985,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_511 ),
    inference(forward_demodulation,[],[f7984,f3346])).

fof(f7984,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_44
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f7983,f443])).

fof(f7983,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_48
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f7982,f456])).

fof(f7982,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f7981,f430])).

fof(f7981,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_52
    | ~ spl7_56
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f7980,f469])).

fof(f7980,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_56
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f7979,f482])).

fof(f7979,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_36
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f7978,f417])).

fof(f7978,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f7977,f192])).

fof(f7977,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_511 ),
    inference(resolution,[],[f5570,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_7(X2,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5570,plain,
    ( ~ v13_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_511 ),
    inference(avatar_component_clause,[],[f5569])).

fof(f5569,plain,
    ( spl7_511
  <=> ~ v13_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_511])])).

fof(f7949,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(avatar_contradiction_clause,[],[f7948])).

fof(f7948,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7947,f98])).

fof(f7947,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7946,f99])).

fof(f7946,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7945,f100])).

fof(f7945,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7944,f101])).

fof(f7944,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7943,f102])).

fof(f7943,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7942,f103])).

fof(f7942,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7941,f196])).

fof(f7941,plain,
    ( ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7940,f202])).

fof(f7940,plain,
    ( ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7935,f864])).

fof(f7935,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(resolution,[],[f7934,f208])).

fof(f7934,plain,
    ( ! [X0] :
        ( ~ v2_waybel_7(sK1,X0)
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510
    | ~ spl7_640 ),
    inference(subsumption_resolution,[],[f7838,f7784])).

fof(f7838,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f7837,f864])).

fof(f7837,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f7836,f861])).

fof(f7836,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f7835,f3346])).

fof(f7835,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_44
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7834,f443])).

fof(f7834,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_48
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7833,f456])).

fof(f7833,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7832,f430])).

fof(f7832,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_52
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7831,f469])).

fof(f7831,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_56
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7830,f482])).

fof(f7830,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7829,f417])).

fof(f7829,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7828,f192])).

fof(f7828,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
        | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(resolution,[],[f7826,f143])).

fof(f7826,plain,
    ( ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7825,f214])).

fof(f7825,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f7824,f861])).

fof(f7824,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7823,f452])).

fof(f7823,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7822,f465])).

fof(f7822,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7821,f439])).

fof(f7821,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7820,f491])).

fof(f7820,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7819,f478])).

fof(f7819,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_11
    | ~ spl7_30
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7818,f359])).

fof(f7818,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_11
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7817,f192])).

fof(f7817,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_11
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7816,f5561])).

fof(f7816,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_11
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7815,f5567])).

fof(f7815,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_waybel_7(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_11 ),
    inference(resolution,[],[f229,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v2_waybel_7(X1,k7_lattice3(X0))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ v2_waybel_0(X1,k7_lattice3(X0))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f229,plain,
    ( ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl7_11
  <=> ~ v1_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f7785,plain,
    ( ~ spl7_3
    | spl7_640
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f7781,f863,f213,f207,f195,f7783,f204])).

fof(f204,plain,
    ( spl7_3
  <=> ~ v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f7781,plain,
    ( ! [X2] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2) )
    | ~ spl7_0
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7451,f196])).

fof(f7451,plain,
    ( ! [X2] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ v2_waybel_0(sK1,sK0)
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2) )
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f7450,f864])).

fof(f7450,plain,
    ( ! [X2] :
        ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ v2_waybel_0(sK1,sK0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2) )
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f7449,f98])).

fof(f7449,plain,
    ( ! [X2] :
        ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ v2_waybel_0(sK1,sK0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ v3_orders_2(sK0) )
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f7448,f99])).

fof(f7448,plain,
    ( ! [X2] :
        ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ v2_waybel_0(sK1,sK0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f7447,f100])).

fof(f7447,plain,
    ( ! [X2] :
        ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ v2_waybel_0(sK1,sK0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f7446,f101])).

fof(f7446,plain,
    ( ! [X2] :
        ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ v2_waybel_0(sK1,sK0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f7445,f102])).

fof(f7445,plain,
    ( ! [X2] :
        ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ v2_waybel_0(sK1,sK0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f7444,f103])).

fof(f7444,plain,
    ( ! [X2] :
        ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ v2_waybel_0(sK1,sK0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f7443,f192])).

fof(f7443,plain,
    ( ! [X2] :
        ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ v2_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f7010,f214])).

fof(f7010,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ v2_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f208,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_waybel_7(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f7771,plain,
    ( spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(avatar_contradiction_clause,[],[f7770])).

fof(f7770,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7769,f864])).

fof(f7769,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f7768,f861])).

fof(f7768,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f7767,f3346])).

fof(f7767,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7766,f452])).

fof(f7766,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7765,f465])).

fof(f7765,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7764,f439])).

fof(f7764,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7763,f491])).

fof(f7763,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7762,f478])).

fof(f7762,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7761,f359])).

fof(f7761,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7760,f226])).

fof(f226,plain,
    ( v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl7_10
  <=> v1_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f7760,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7759,f232])).

fof(f232,plain,
    ( v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl7_12
  <=> v12_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f7759,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7758,f244])).

fof(f244,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl7_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f7758,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7757,f5561])).

fof(f7757,plain,
    ( ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7754,f5567])).

fof(f7754,plain,
    ( ~ v13_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(resolution,[],[f7504,f238])).

fof(f238,plain,
    ( v1_waybel_7(sK1,k7_lattice3(sK0))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl7_14
  <=> v1_waybel_7(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f7504,plain,
    ( ! [X0] :
        ( ~ v1_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7503,f168])).

fof(f168,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',fc1_yellow_7)).

fof(f7503,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7502,f170])).

fof(f170,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',fc2_yellow_7)).

fof(f7502,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7501,f166])).

fof(f166,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',fc3_yellow_7)).

fof(f7501,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7500,f174])).

fof(f174,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',fc5_yellow_7)).

fof(f7500,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7499,f172])).

fof(f172,plain,(
    ! [X0] :
      ( v2_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0) )
     => ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',fc6_yellow_7)).

fof(f7499,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_lattice3(k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7498,f137])).

fof(f7498,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ l1_orders_2(k7_lattice3(X0))
        | ~ v2_lattice3(k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7494,f192])).

fof(f7494,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ l1_orders_2(k7_lattice3(X0))
        | ~ v2_lattice3(k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(resolution,[],[f7470,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f7470,plain,
    ( ! [X0] :
        ( ~ v2_waybel_7(sK1,X0)
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7469,f6611])).

fof(f6611,plain,
    ( ! [X2] :
        ( ~ v2_lattice3(X2)
        | ~ l1_orders_2(X2)
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f6610,f864])).

fof(f6610,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f6209,f3346])).

fof(f6209,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102 ),
    inference(forward_demodulation,[],[f3642,f861])).

fof(f3642,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f3641,f452])).

fof(f3641,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f3640,f465])).

fof(f3640,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_54
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f3639,f439])).

fof(f3639,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f3638,f491])).

fof(f3638,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f3637,f478])).

fof(f3637,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v2_lattice3(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f3636,f359])).

fof(f3636,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v2_lattice3(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f3635,f226])).

fof(f3635,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v2_lattice3(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f3634,f232])).

fof(f3634,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
        | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v2_lattice3(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f3633,f244])).

fof(f3633,plain,
    ( ! [X2] :
        ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
        | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v2_lattice3(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f3625,f192])).

fof(f3625,plain,
    ( ! [X2] :
        ( v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
        | ~ l1_orders_2(X2)
        | ~ v2_lattice3(X2)
        | ~ v1_lattice3(X2)
        | ~ v5_orders_2(X2)
        | ~ v4_orders_2(X2)
        | ~ v3_orders_2(X2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
        | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v2_lattice3(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f2836,f238])).

fof(f2836,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_waybel_7(X2,X3)
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(k7_lattice3(X3)),u1_orders_2(k7_lattice3(X3)))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v12_waybel_0(X2,X3)
      | ~ v1_waybel_0(X2,X3)
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f2835,f168])).

fof(f2835,plain,(
    ! [X4,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(k7_lattice3(X3)),u1_orders_2(k7_lattice3(X3)))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ v3_orders_2(k7_lattice3(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v1_waybel_7(X2,X3)
      | ~ v12_waybel_0(X2,X3)
      | ~ v1_waybel_0(X2,X3)
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f2834,f170])).

fof(f2834,plain,(
    ! [X4,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(k7_lattice3(X3)),u1_orders_2(k7_lattice3(X3)))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ v4_orders_2(k7_lattice3(X3))
      | ~ v3_orders_2(k7_lattice3(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v1_waybel_7(X2,X3)
      | ~ v12_waybel_0(X2,X3)
      | ~ v1_waybel_0(X2,X3)
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f2833,f166])).

fof(f2833,plain,(
    ! [X4,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(k7_lattice3(X3)),u1_orders_2(k7_lattice3(X3)))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ v5_orders_2(k7_lattice3(X3))
      | ~ v4_orders_2(k7_lattice3(X3))
      | ~ v3_orders_2(k7_lattice3(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v1_waybel_7(X2,X3)
      | ~ v12_waybel_0(X2,X3)
      | ~ v1_waybel_0(X2,X3)
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f2832,f174])).

fof(f2832,plain,(
    ! [X4,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(k7_lattice3(X3)),u1_orders_2(k7_lattice3(X3)))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ v1_lattice3(k7_lattice3(X3))
      | ~ v5_orders_2(k7_lattice3(X3))
      | ~ v4_orders_2(k7_lattice3(X3))
      | ~ v3_orders_2(k7_lattice3(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v1_waybel_7(X2,X3)
      | ~ v12_waybel_0(X2,X3)
      | ~ v1_waybel_0(X2,X3)
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f2831,f172])).

fof(f2831,plain,(
    ! [X4,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(k7_lattice3(X3)),u1_orders_2(k7_lattice3(X3)))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ v2_lattice3(k7_lattice3(X3))
      | ~ v1_lattice3(k7_lattice3(X3))
      | ~ v5_orders_2(k7_lattice3(X3))
      | ~ v4_orders_2(k7_lattice3(X3))
      | ~ v3_orders_2(k7_lattice3(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v1_waybel_7(X2,X3)
      | ~ v12_waybel_0(X2,X3)
      | ~ v1_waybel_0(X2,X3)
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f2830,f137])).

fof(f2830,plain,(
    ! [X4,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(k7_lattice3(X3)),u1_orders_2(k7_lattice3(X3)))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ l1_orders_2(k7_lattice3(X3))
      | ~ v2_lattice3(k7_lattice3(X3))
      | ~ v1_lattice3(k7_lattice3(X3))
      | ~ v5_orders_2(k7_lattice3(X3))
      | ~ v4_orders_2(k7_lattice3(X3))
      | ~ v3_orders_2(k7_lattice3(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v1_waybel_7(X2,X3)
      | ~ v12_waybel_0(X2,X3)
      | ~ v1_waybel_0(X2,X3)
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f2829,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f2829,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X3))))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(k7_lattice3(X3)),u1_orders_2(k7_lattice3(X3)))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ l1_orders_2(k7_lattice3(X3))
      | ~ v2_lattice3(k7_lattice3(X3))
      | ~ v1_lattice3(k7_lattice3(X3))
      | ~ v5_orders_2(k7_lattice3(X3))
      | ~ v4_orders_2(k7_lattice3(X3))
      | ~ v3_orders_2(k7_lattice3(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v1_waybel_7(X2,X3)
      | ~ v12_waybel_0(X2,X3)
      | ~ v1_waybel_0(X2,X3)
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f2828,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f2828,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X3))))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v13_waybel_0(X2,k7_lattice3(X3))
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(k7_lattice3(X3)),u1_orders_2(k7_lattice3(X3)))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ l1_orders_2(k7_lattice3(X3))
      | ~ v2_lattice3(k7_lattice3(X3))
      | ~ v1_lattice3(k7_lattice3(X3))
      | ~ v5_orders_2(k7_lattice3(X3))
      | ~ v4_orders_2(k7_lattice3(X3))
      | ~ v3_orders_2(k7_lattice3(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v1_waybel_7(X2,X3)
      | ~ v12_waybel_0(X2,X3)
      | ~ v1_waybel_0(X2,X3)
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f2822,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X1,X0)
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f2822,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X3))))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v13_waybel_0(X2,k7_lattice3(X3))
      | ~ v2_waybel_0(X2,k7_lattice3(X3))
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(k7_lattice3(X3)),u1_orders_2(k7_lattice3(X3)))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ l1_orders_2(k7_lattice3(X3))
      | ~ v2_lattice3(k7_lattice3(X3))
      | ~ v1_lattice3(k7_lattice3(X3))
      | ~ v5_orders_2(k7_lattice3(X3))
      | ~ v4_orders_2(k7_lattice3(X3))
      | ~ v3_orders_2(k7_lattice3(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v1_waybel_7(X2,X3)
      | ~ v12_waybel_0(X2,X3)
      | ~ v1_waybel_0(X2,X3)
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f2819])).

fof(f2819,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k7_lattice3(X3))))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v13_waybel_0(X2,k7_lattice3(X3))
      | ~ v2_waybel_0(X2,k7_lattice3(X3))
      | v1_xboole_0(X2)
      | g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) != g1_orders_2(u1_struct_0(k7_lattice3(X3)),u1_orders_2(k7_lattice3(X3)))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ l1_orders_2(k7_lattice3(X3))
      | ~ v2_lattice3(k7_lattice3(X3))
      | ~ v1_lattice3(k7_lattice3(X3))
      | ~ v5_orders_2(k7_lattice3(X3))
      | ~ v4_orders_2(k7_lattice3(X3))
      | ~ v3_orders_2(k7_lattice3(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v1_waybel_7(X2,X3)
      | ~ v12_waybel_0(X2,X3)
      | ~ v1_waybel_0(X2,X3)
      | v1_xboole_0(X2)
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(resolution,[],[f144,f148])).

fof(f7469,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f7468,f864])).

fof(f7468,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f7467,f98])).

fof(f7467,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f7466,f99])).

fof(f7466,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f7465,f100])).

fof(f7465,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f7464,f101])).

fof(f7464,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f7463,f102])).

fof(f7463,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f7462,f103])).

fof(f7462,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f7461,f192])).

fof(f7461,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f205,f142])).

fof(f205,plain,
    ( ~ v13_waybel_0(sK1,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f204])).

fof(f7441,plain,
    ( spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(avatar_contradiction_clause,[],[f7440])).

fof(f7440,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7439,f864])).

fof(f7439,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f7438,f861])).

fof(f7438,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f7437,f3346])).

fof(f7437,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7436,f452])).

fof(f7436,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7435,f465])).

fof(f7435,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7434,f439])).

fof(f7434,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7433,f491])).

fof(f7433,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7432,f478])).

fof(f7432,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7431,f359])).

fof(f7431,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7430,f226])).

fof(f7430,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7429,f232])).

fof(f7429,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7428,f244])).

fof(f7428,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7427,f5561])).

fof(f7427,plain,
    ( ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f7424,f5567])).

fof(f7424,plain,
    ( ~ v13_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(resolution,[],[f7022,f238])).

fof(f7022,plain,
    ( ! [X0] :
        ( ~ v1_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7021,f168])).

fof(f7021,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7020,f170])).

fof(f7020,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7019,f166])).

fof(f7019,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7018,f174])).

fof(f7018,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7017,f172])).

fof(f7017,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_lattice3(k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7016,f137])).

fof(f7016,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ l1_orders_2(k7_lattice3(X0))
        | ~ v2_lattice3(k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7012,f192])).

fof(f7012,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ l1_orders_2(k7_lattice3(X0))
        | ~ v2_lattice3(k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(resolution,[],[f7007,f148])).

fof(f7007,plain,
    ( ! [X0] :
        ( ~ v2_waybel_7(sK1,X0)
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f7006,f6611])).

fof(f7006,plain,
    ( ! [X0] :
        ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f7005,f864])).

fof(f7005,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f7004,f98])).

fof(f7004,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f7003,f99])).

fof(f7003,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f7002,f100])).

fof(f7002,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f7001,f101])).

fof(f7001,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f7000,f102])).

fof(f7000,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f6999,f103])).

fof(f6999,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f6998,f192])).

fof(f6998,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_1 ),
    inference(resolution,[],[f199,f141])).

fof(f199,plain,
    ( ~ v2_waybel_0(sK1,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl7_1
  <=> ~ v2_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f6996,plain,
    ( spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(avatar_contradiction_clause,[],[f6995])).

fof(f6995,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6994,f214])).

fof(f6994,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f6993,f861])).

fof(f6993,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6992,f864])).

fof(f6992,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f6991,f861])).

fof(f6991,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_36
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(forward_demodulation,[],[f6990,f3346])).

fof(f6990,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6989,f452])).

fof(f6989,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6988,f465])).

fof(f6988,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6987,f439])).

fof(f6987,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6986,f491])).

fof(f6986,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6985,f478])).

fof(f6985,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6984,f359])).

fof(f6984,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6983,f226])).

fof(f6983,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6982,f232])).

fof(f6982,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6981,f244])).

fof(f6981,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_104
    | ~ spl7_508
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6980,f5561])).

fof(f6980,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_104
    | ~ spl7_510 ),
    inference(subsumption_resolution,[],[f6977,f5567])).

fof(f6977,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_104 ),
    inference(resolution,[],[f6460,f238])).

fof(f6460,plain,
    ( ! [X0] :
        ( ~ v1_waybel_7(sK1,X0)
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f6459,f168])).

fof(f6459,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f6458,f170])).

fof(f6458,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f6457,f166])).

fof(f6457,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f6456,f174])).

fof(f6456,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f6455,f172])).

fof(f6455,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_lattice3(k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f6454,f137])).

fof(f6454,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ l1_orders_2(k7_lattice3(X0))
        | ~ v2_lattice3(k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f6450,f192])).

fof(f6450,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(X0))
        | ~ v2_waybel_0(sK1,k7_lattice3(X0))
        | ~ l1_orders_2(k7_lattice3(X0))
        | ~ v2_lattice3(k7_lattice3(X0))
        | ~ v1_lattice3(k7_lattice3(X0))
        | ~ v5_orders_2(k7_lattice3(X0))
        | ~ v4_orders_2(k7_lattice3(X0))
        | ~ v3_orders_2(k7_lattice3(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_7(sK1,X0)
        | ~ v12_waybel_0(sK1,X0)
        | ~ v1_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5
    | ~ spl7_104 ),
    inference(resolution,[],[f6338,f148])).

fof(f6338,plain,
    ( ! [X0] :
        ( ~ v2_waybel_7(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f6217,f864])).

fof(f6217,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f6216,f98])).

fof(f6216,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f6215,f99])).

fof(f6215,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f6214,f100])).

fof(f6214,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f6213,f101])).

fof(f6213,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f6212,f102])).

fof(f6212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f6211,f103])).

fof(f6211,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f6210,f192])).

fof(f6210,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(sK1,X0)
        | ~ v13_waybel_0(sK1,X0)
        | ~ v2_waybel_0(sK1,X0)
        | v1_xboole_0(sK1)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f211,f143])).

fof(f211,plain,
    ( ~ v2_waybel_7(sK1,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl7_5
  <=> ~ v2_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f6137,plain,(
    ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f6136])).

fof(f6136,plain,
    ( $false
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f223,f192])).

fof(f223,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl7_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f5610,plain,
    ( ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | spl7_511 ),
    inference(avatar_contradiction_clause,[],[f5609])).

fof(f5609,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f5608,f452])).

fof(f5608,plain,
    ( ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f5607,f465])).

fof(f5607,plain,
    ( ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f5606,f439])).

fof(f5606,plain,
    ( ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f5605,f491])).

fof(f5605,plain,
    ( ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f5604,f478])).

fof(f5604,plain,
    ( ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f5603,f359])).

fof(f5603,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f5602,f192])).

fof(f5602,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f5601,f226])).

fof(f5601,plain,
    ( ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f5600,f232])).

fof(f5600,plain,
    ( ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f5599,f238])).

fof(f5599,plain,
    ( ~ v1_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_16
    | ~ spl7_511 ),
    inference(subsumption_resolution,[],[f5597,f244])).

fof(f5597,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v1_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_511 ),
    inference(resolution,[],[f5570,f147])).

fof(f5586,plain,
    ( ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | spl7_509 ),
    inference(avatar_contradiction_clause,[],[f5585])).

fof(f5585,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f5584,f452])).

fof(f5584,plain,
    ( ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f5583,f465])).

fof(f5583,plain,
    ( ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f5582,f439])).

fof(f5582,plain,
    ( ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f5581,f491])).

fof(f5581,plain,
    ( ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f5580,f478])).

fof(f5580,plain,
    ( ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_30
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f5579,f359])).

fof(f5579,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f5578,f192])).

fof(f5578,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f5577,f226])).

fof(f5577,plain,
    ( ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f5576,f232])).

fof(f5576,plain,
    ( ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f5575,f238])).

fof(f5575,plain,
    ( ~ v1_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_16
    | ~ spl7_509 ),
    inference(subsumption_resolution,[],[f5573,f244])).

fof(f5573,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v1_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_509 ),
    inference(resolution,[],[f5564,f146])).

fof(f1792,plain,
    ( ~ spl7_17
    | spl7_6
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f1791,f860,f490,f477,f464,f451,f438,f358,f237,f231,f225,f213,f246])).

fof(f1791,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58
    | ~ spl7_102 ),
    inference(forward_demodulation,[],[f1790,f861])).

fof(f1790,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f1789,f452])).

fof(f1789,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_50
    | ~ spl7_54
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f1788,f465])).

fof(f1788,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_30
    | ~ spl7_42
    | ~ spl7_54
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f1787,f439])).

fof(f1787,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_30
    | ~ spl7_54
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f1786,f491])).

fof(f1786,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_30
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f1785,f478])).

fof(f1785,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f1784,f359])).

fof(f1784,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f1783,f192])).

fof(f1783,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f1782,f226])).

fof(f1782,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f1781,f232])).

fof(f1781,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(k7_lattice3(sK0)))))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_14 ),
    inference(resolution,[],[f238,f149])).

fof(f918,plain,(
    spl7_105 ),
    inference(avatar_contradiction_clause,[],[f917])).

fof(f917,plain,
    ( $false
    | ~ spl7_105 ),
    inference(subsumption_resolution,[],[f916,f103])).

fof(f916,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_105 ),
    inference(trivial_inequality_removal,[],[f915])).

fof(f915,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != k7_lattice3(k7_lattice3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_105 ),
    inference(superposition,[],[f867,f134])).

fof(f134,plain,(
    ! [X0] :
      ( k7_lattice3(k7_lattice3(X0)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k7_lattice3(k7_lattice3(X0)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(k7_lattice3(X0)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',t8_lattice3)).

fof(f867,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ spl7_105 ),
    inference(avatar_component_clause,[],[f866])).

fof(f866,plain,
    ( spl7_105
  <=> k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f868,plain,
    ( spl7_102
    | ~ spl7_105
    | ~ spl7_36
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f850,f497,f416,f866,f860])).

fof(f497,plain,
    ( spl7_60
  <=> v1_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f850,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_36
    | ~ spl7_60 ),
    inference(superposition,[],[f842,f529])).

fof(f529,plain,
    ( k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ spl7_36
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f528,f417])).

fof(f528,plain,
    ( k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(k7_lattice3(k7_lattice3(sK0))),u1_orders_2(k7_lattice3(k7_lattice3(sK0))))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_60 ),
    inference(resolution,[],[f498,f139])).

fof(f498,plain,
    ( v1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f497])).

fof(f842,plain,(
    ! [X19,X18] :
      ( g1_orders_2(X18,X19) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK0) = X18 ) ),
    inference(resolution,[],[f822,f103])).

fof(f822,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(X1,X2) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) ),
    inference(resolution,[],[f181,f135])).

fof(f181,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f549,plain,
    ( ~ spl7_30
    | spl7_57 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | ~ spl7_30
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f547,f102])).

fof(f547,plain,
    ( ~ v2_lattice3(sK0)
    | ~ spl7_30
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f546,f103])).

fof(f546,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ spl7_30
    | ~ spl7_57 ),
    inference(resolution,[],[f527,f174])).

fof(f527,plain,
    ( ~ v1_lattice3(k7_lattice3(sK0))
    | ~ spl7_30
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f526,f359])).

fof(f526,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ spl7_57 ),
    inference(resolution,[],[f485,f172])).

fof(f485,plain,
    ( ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl7_57
  <=> ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f545,plain,
    ( ~ spl7_30
    | spl7_53 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | ~ spl7_30
    | ~ spl7_53 ),
    inference(subsumption_resolution,[],[f543,f101])).

fof(f543,plain,
    ( ~ v1_lattice3(sK0)
    | ~ spl7_30
    | ~ spl7_53 ),
    inference(subsumption_resolution,[],[f542,f103])).

fof(f542,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ spl7_30
    | ~ spl7_53 ),
    inference(resolution,[],[f525,f172])).

fof(f525,plain,
    ( ~ v2_lattice3(k7_lattice3(sK0))
    | ~ spl7_30
    | ~ spl7_53 ),
    inference(subsumption_resolution,[],[f524,f359])).

fof(f524,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v2_lattice3(k7_lattice3(sK0))
    | ~ spl7_53 ),
    inference(resolution,[],[f472,f174])).

fof(f472,plain,
    ( ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl7_53
  <=> ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f541,plain,
    ( ~ spl7_30
    | spl7_49 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | ~ spl7_30
    | ~ spl7_49 ),
    inference(subsumption_resolution,[],[f539,f99])).

fof(f539,plain,
    ( ~ v4_orders_2(sK0)
    | ~ spl7_30
    | ~ spl7_49 ),
    inference(subsumption_resolution,[],[f538,f103])).

fof(f538,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ spl7_30
    | ~ spl7_49 ),
    inference(resolution,[],[f523,f170])).

fof(f523,plain,
    ( ~ v4_orders_2(k7_lattice3(sK0))
    | ~ spl7_30
    | ~ spl7_49 ),
    inference(subsumption_resolution,[],[f522,f359])).

fof(f522,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ spl7_49 ),
    inference(resolution,[],[f459,f170])).

fof(f459,plain,
    ( ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl7_49
  <=> ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f537,plain,
    ( ~ spl7_30
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f536])).

fof(f536,plain,
    ( $false
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f535,f98])).

fof(f535,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f534,f103])).

fof(f534,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(resolution,[],[f521,f168])).

fof(f521,plain,
    ( ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_30
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f520,f359])).

fof(f520,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl7_45 ),
    inference(resolution,[],[f446,f168])).

fof(f446,plain,
    ( ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl7_45
  <=> ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f533,plain,
    ( ~ spl7_30
    | spl7_41 ),
    inference(avatar_contradiction_clause,[],[f532])).

fof(f532,plain,
    ( $false
    | ~ spl7_30
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f531,f100])).

fof(f531,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl7_30
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f530,f103])).

fof(f530,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl7_30
    | ~ spl7_41 ),
    inference(resolution,[],[f519,f166])).

fof(f519,plain,
    ( ~ v5_orders_2(k7_lattice3(sK0))
    | ~ spl7_30
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f518,f359])).

fof(f518,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ spl7_41 ),
    inference(resolution,[],[f433,f166])).

fof(f433,plain,
    ( ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl7_41
  <=> ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f512,plain,(
    spl7_37 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f509,f103])).

fof(f509,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_37 ),
    inference(resolution,[],[f420,f323])).

fof(f323,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(global_subsumption,[],[f135,f321])).

fof(f321,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(k7_lattice3(X0)))
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f180,f134])).

fof(f180,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t21_waybel_7.p',dt_g1_orders_2)).

fof(f420,plain,
    ( ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl7_37
  <=> ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f499,plain,
    ( ~ spl7_37
    | spl7_60 ),
    inference(avatar_split_clause,[],[f412,f497,f419])).

fof(f412,plain,
    ( v1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    inference(superposition,[],[f324,f400])).

fof(f400,plain,(
    k7_lattice3(sK0) = k7_lattice3(k7_lattice3(k7_lattice3(sK0))) ),
    inference(resolution,[],[f394,f103])).

fof(f394,plain,(
    ! [X1] :
      ( ~ l1_orders_2(X1)
      | k7_lattice3(X1) = k7_lattice3(k7_lattice3(k7_lattice3(X1))) ) ),
    inference(subsumption_resolution,[],[f390,f137])).

fof(f390,plain,(
    ! [X1] :
      ( k7_lattice3(X1) = k7_lattice3(k7_lattice3(k7_lattice3(X1)))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(k7_lattice3(X1)) ) ),
    inference(superposition,[],[f329,f134])).

fof(f324,plain,(
    ! [X1] :
      ( v1_orders_2(k7_lattice3(k7_lattice3(X1)))
      | ~ l1_orders_2(X1) ) ),
    inference(global_subsumption,[],[f135,f322])).

fof(f322,plain,(
    ! [X1] :
      ( v1_orders_2(k7_lattice3(k7_lattice3(X1)))
      | ~ m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
      | ~ l1_orders_2(X1) ) ),
    inference(superposition,[],[f179,f134])).

fof(f179,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f492,plain,
    ( ~ spl7_57
    | ~ spl7_37
    | spl7_58 ),
    inference(avatar_split_clause,[],[f410,f490,f419,f484])).

fof(f410,plain,
    ( v1_lattice3(k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ v2_lattice3(k7_lattice3(k7_lattice3(sK0))) ),
    inference(superposition,[],[f174,f400])).

fof(f479,plain,
    ( ~ spl7_53
    | ~ spl7_37
    | spl7_54 ),
    inference(avatar_split_clause,[],[f409,f477,f419,f471])).

fof(f409,plain,
    ( v2_lattice3(k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ v1_lattice3(k7_lattice3(k7_lattice3(sK0))) ),
    inference(superposition,[],[f172,f400])).

fof(f466,plain,
    ( ~ spl7_49
    | ~ spl7_37
    | spl7_50 ),
    inference(avatar_split_clause,[],[f408,f464,f419,f458])).

fof(f408,plain,
    ( v4_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ v4_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    inference(superposition,[],[f170,f400])).

fof(f453,plain,
    ( ~ spl7_45
    | ~ spl7_37
    | spl7_46 ),
    inference(avatar_split_clause,[],[f407,f451,f419,f445])).

fof(f407,plain,
    ( v3_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ v3_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    inference(superposition,[],[f168,f400])).

fof(f440,plain,
    ( ~ spl7_41
    | ~ spl7_37
    | spl7_42 ),
    inference(avatar_split_clause,[],[f406,f438,f419,f432])).

fof(f406,plain,
    ( v5_orders_2(k7_lattice3(sK0))
    | ~ l1_orders_2(k7_lattice3(k7_lattice3(sK0)))
    | ~ v5_orders_2(k7_lattice3(k7_lattice3(sK0))) ),
    inference(superposition,[],[f166,f400])).

fof(f379,plain,(
    spl7_31 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f377,f103])).

fof(f377,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_31 ),
    inference(resolution,[],[f362,f137])).

fof(f362,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl7_31
  <=> ~ l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f265,plain,
    ( spl7_0
    | spl7_10 ),
    inference(avatar_split_clause,[],[f110,f225,f195])).

fof(f110,plain,
    ( v1_waybel_0(sK1,k7_lattice3(sK0))
    | v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f264,plain,
    ( spl7_2
    | spl7_10 ),
    inference(avatar_split_clause,[],[f111,f225,f201])).

fof(f111,plain,
    ( v1_waybel_0(sK1,k7_lattice3(sK0))
    | v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f263,plain,
    ( spl7_4
    | spl7_10 ),
    inference(avatar_split_clause,[],[f112,f225,f207])).

fof(f112,plain,
    ( v1_waybel_0(sK1,k7_lattice3(sK0))
    | v2_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f262,plain,
    ( spl7_6
    | spl7_10 ),
    inference(avatar_split_clause,[],[f113,f225,f213])).

fof(f113,plain,
    ( v1_waybel_0(sK1,k7_lattice3(sK0))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f84])).

fof(f261,plain,
    ( spl7_0
    | spl7_12 ),
    inference(avatar_split_clause,[],[f115,f231,f195])).

fof(f115,plain,
    ( v12_waybel_0(sK1,k7_lattice3(sK0))
    | v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f260,plain,
    ( spl7_2
    | spl7_12 ),
    inference(avatar_split_clause,[],[f116,f231,f201])).

fof(f116,plain,
    ( v12_waybel_0(sK1,k7_lattice3(sK0))
    | v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f259,plain,
    ( spl7_4
    | spl7_12 ),
    inference(avatar_split_clause,[],[f117,f231,f207])).

fof(f117,plain,
    ( v12_waybel_0(sK1,k7_lattice3(sK0))
    | v2_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f258,plain,
    ( spl7_6
    | spl7_12 ),
    inference(avatar_split_clause,[],[f118,f231,f213])).

fof(f118,plain,
    ( v12_waybel_0(sK1,k7_lattice3(sK0))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f84])).

fof(f257,plain,
    ( spl7_0
    | spl7_14 ),
    inference(avatar_split_clause,[],[f120,f237,f195])).

fof(f120,plain,
    ( v1_waybel_7(sK1,k7_lattice3(sK0))
    | v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f256,plain,
    ( spl7_2
    | spl7_14 ),
    inference(avatar_split_clause,[],[f121,f237,f201])).

fof(f121,plain,
    ( v1_waybel_7(sK1,k7_lattice3(sK0))
    | v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f255,plain,
    ( spl7_4
    | spl7_14 ),
    inference(avatar_split_clause,[],[f122,f237,f207])).

fof(f122,plain,
    ( v1_waybel_7(sK1,k7_lattice3(sK0))
    | v2_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f254,plain,
    ( spl7_6
    | spl7_14 ),
    inference(avatar_split_clause,[],[f123,f237,f213])).

fof(f123,plain,
    ( v1_waybel_7(sK1,k7_lattice3(sK0))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f84])).

fof(f252,plain,
    ( spl7_0
    | spl7_16 ),
    inference(avatar_split_clause,[],[f125,f243,f195])).

fof(f125,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f251,plain,
    ( spl7_2
    | spl7_16 ),
    inference(avatar_split_clause,[],[f126,f243,f201])).

fof(f126,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f250,plain,
    ( spl7_4
    | spl7_16 ),
    inference(avatar_split_clause,[],[f127,f243,f207])).

fof(f127,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | v2_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f249,plain,
    ( spl7_6
    | spl7_16 ),
    inference(avatar_split_clause,[],[f128,f243,f213])).

fof(f128,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f84])).

fof(f248,plain,
    ( ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_7
    | spl7_8
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f193,f246,f240,f234,f228,f222,f216,f210,f204,f198])).

fof(f216,plain,
    ( spl7_7
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f193,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v1_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_7(sK1,sK0)
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v1_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v12_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v1_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_7(sK1,sK0)
    | ~ v13_waybel_0(sK1,sK0)
    | ~ v2_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f84])).
%------------------------------------------------------------------------------
