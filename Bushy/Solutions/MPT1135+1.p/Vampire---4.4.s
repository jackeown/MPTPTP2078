%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t66_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:46 EDT 2019

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 275 expanded)
%              Number of leaves         :   31 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  450 ( 930 expanded)
%              Number of equality atoms :   67 ( 178 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3503,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f143,f150,f166,f196,f247,f292,f453,f458,f526,f627,f661,f674,f1070,f1389,f2754,f3472,f3487,f3502])).

fof(f3502,plain,
    ( ~ spl9_18
    | spl9_159
    | ~ spl9_392 ),
    inference(avatar_contradiction_clause,[],[f3501])).

fof(f3501,plain,
    ( $false
    | ~ spl9_18
    | ~ spl9_159
    | ~ spl9_392 ),
    inference(unit_resulting_resolution,[],[f195,f1113,f2753])).

fof(f2753,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)) )
    | ~ spl9_392 ),
    inference(avatar_component_clause,[],[f2752])).

fof(f2752,plain,
    ( spl9_392
  <=> ! [X1] :
        ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_392])])).

fof(f1113,plain,
    ( ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl9_159 ),
    inference(avatar_component_clause,[],[f1112])).

fof(f1112,plain,
    ( spl9_159
  <=> ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_159])])).

fof(f195,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl9_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f3487,plain,
    ( ~ spl9_0
    | ~ spl9_8
    | spl9_153
    | ~ spl9_192
    | ~ spl9_466 ),
    inference(avatar_contradiction_clause,[],[f3486])).

fof(f3486,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_8
    | ~ spl9_153
    | ~ spl9_192
    | ~ spl9_466 ),
    inference(subsumption_resolution,[],[f3485,f121])).

fof(f121,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl9_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f3485,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_8
    | ~ spl9_153
    | ~ spl9_192
    | ~ spl9_466 ),
    inference(subsumption_resolution,[],[f3484,f1069])).

fof(f1069,plain,
    ( k1_pre_topc(sK0,sK1) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_153 ),
    inference(avatar_component_clause,[],[f1068])).

fof(f1068,plain,
    ( spl9_153
  <=> k1_pre_topc(sK0,sK1) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_153])])).

fof(f3484,plain,
    ( k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_8
    | ~ spl9_192
    | ~ spl9_466 ),
    inference(subsumption_resolution,[],[f3481,f149])).

fof(f149,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl9_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f3481,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_192
    | ~ spl9_466 ),
    inference(resolution,[],[f3471,f1380])).

fof(f1380,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(X0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_192 ),
    inference(avatar_component_clause,[],[f1379])).

fof(f1379,plain,
    ( spl9_192
  <=> ! [X0] :
        ( k1_pre_topc(X0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_192])])).

fof(f3471,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ spl9_466 ),
    inference(avatar_component_clause,[],[f3470])).

fof(f3470,plain,
    ( spl9_466
  <=> m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_466])])).

fof(f3472,plain,
    ( spl9_466
    | ~ spl9_0
    | ~ spl9_18
    | ~ spl9_158 ),
    inference(avatar_split_clause,[],[f3217,f1109,f194,f120,f3470])).

fof(f1109,plain,
    ( spl9_158
  <=> l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).

fof(f3217,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ spl9_0
    | ~ spl9_18
    | ~ spl9_158 ),
    inference(subsumption_resolution,[],[f3216,f195])).

fof(f3216,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl9_0
    | ~ spl9_158 ),
    inference(subsumption_resolution,[],[f3209,f121])).

fof(f3209,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl9_158 ),
    inference(resolution,[],[f1110,f566])).

fof(f566,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)),X5))
      | ~ l1_pre_topc(X4)
      | m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)),X5),X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))) ) ),
    inference(subsumption_resolution,[],[f257,f211])).

fof(f211,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f99,f84])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t66_pre_topc.p',dt_u1_pre_topc)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t66_pre_topc.p',dt_g1_pre_topc)).

fof(f257,plain,(
    ! [X4,X5] :
      ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)),X5),X4)
      | ~ l1_pre_topc(X4)
      | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)),X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))) ) ),
    inference(resolution,[],[f87,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t66_pre_topc.p',dt_k1_pre_topc)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t66_pre_topc.p',t65_pre_topc)).

fof(f1110,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl9_158 ),
    inference(avatar_component_clause,[],[f1109])).

fof(f2754,plain,
    ( spl9_392
    | ~ spl9_62
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f681,f659,f442,f2752])).

fof(f442,plain,
    ( spl9_62
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f659,plain,
    ( spl9_98
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).

fof(f681,plain,
    ( ! [X1] :
        ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl9_62
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f678,f443])).

fof(f443,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f442])).

fof(f678,plain,
    ( ! [X1] :
        ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl9_98 ),
    inference(resolution,[],[f660,f103])).

fof(f660,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | l1_pre_topc(X0) )
    | ~ spl9_98 ),
    inference(avatar_component_clause,[],[f659])).

fof(f1389,plain,
    ( spl9_192
    | ~ spl9_64
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f1033,f524,f451,f1379])).

fof(f451,plain,
    ( spl9_64
  <=> v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f524,plain,
    ( spl9_74
  <=> k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f1033,plain,
    ( ! [X0] :
        ( k1_pre_topc(X0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_64
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f1032,f525])).

fof(f525,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | ~ spl9_74 ),
    inference(avatar_component_clause,[],[f524])).

fof(f1032,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X0,k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl9_64
    | ~ spl9_74 ),
    inference(subsumption_resolution,[],[f1030,f452])).

fof(f452,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f451])).

fof(f1030,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
        | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X0,k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl9_74 ),
    inference(superposition,[],[f112,f525])).

fof(f112,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | k1_pre_topc(X0,k2_struct_0(X2)) = X2
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_pre_topc(X0,X1) = X2
      | k2_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t66_pre_topc.p',d10_pre_topc)).

fof(f1070,plain,
    ( ~ spl9_153
    | ~ spl9_26
    | spl9_37
    | ~ spl9_100 ),
    inference(avatar_split_clause,[],[f1052,f672,f290,f245,f1068])).

fof(f245,plain,
    ( spl9_26
  <=> v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f290,plain,
    ( spl9_37
  <=> g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f672,plain,
    ( spl9_100
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f1052,plain,
    ( k1_pre_topc(sK0,sK1) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_100 ),
    inference(backward_demodulation,[],[f881,f291])).

fof(f291,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f290])).

fof(f881,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1)
    | ~ spl9_26
    | ~ spl9_100 ),
    inference(subsumption_resolution,[],[f249,f673])).

fof(f673,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl9_100 ),
    inference(avatar_component_clause,[],[f672])).

fof(f249,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl9_26 ),
    inference(resolution,[],[f246,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t66_pre_topc.p',abstractness_v1_pre_topc)).

fof(f246,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f245])).

fof(f674,plain,
    ( spl9_100
    | ~ spl9_8
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f666,f625,f148,f672])).

fof(f625,plain,
    ( spl9_88
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | l1_pre_topc(k1_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f666,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl9_8
    | ~ spl9_88 ),
    inference(resolution,[],[f626,f149])).

fof(f626,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | l1_pre_topc(k1_pre_topc(sK0,X0)) )
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f625])).

fof(f661,plain,
    ( spl9_98
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f460,f442,f659])).

fof(f460,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | l1_pre_topc(X0) )
    | ~ spl9_62 ),
    inference(resolution,[],[f443,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t66_pre_topc.p',dt_m1_pre_topc)).

fof(f627,plain,
    ( spl9_88
    | ~ spl9_0
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f239,f164,f120,f625])).

fof(f164,plain,
    ( spl9_12
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | l1_pre_topc(k1_pre_topc(sK0,X0)) )
    | ~ spl9_0
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f237,f121])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | l1_pre_topc(k1_pre_topc(sK0,X0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f103,f165])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f526,plain,
    ( spl9_74
    | ~ spl9_18
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f512,f442,f194,f524])).

fof(f512,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | ~ spl9_18
    | ~ spl9_62 ),
    inference(subsumption_resolution,[],[f314,f443])).

fof(f314,plain,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) = sK1
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_18 ),
    inference(resolution,[],[f304,f195])).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f303,f103])).

fof(f303,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f113,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f458,plain,
    ( ~ spl9_0
    | spl9_63 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_63 ),
    inference(subsumption_resolution,[],[f455,f121])).

fof(f455,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_63 ),
    inference(resolution,[],[f446,f211])).

fof(f446,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_63 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl9_63
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).

fof(f453,plain,
    ( ~ spl9_63
    | spl9_64
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f232,f194,f451,f445])).

fof(f232,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_18 ),
    inference(resolution,[],[f102,f195])).

fof(f292,plain,
    ( ~ spl9_37
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f278,f141,f290])).

fof(f141,plain,
    ( spl9_6
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f278,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f80,f142])).

fof(f142,plain,
    ( sK1 = sK2
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f141])).

fof(f80,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2)
    & sK1 = sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f61,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
                & X1 = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,X1)),u1_pre_topc(k1_pre_topc(sK0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,sK1)),u1_pre_topc(k1_pre_topc(X0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
            & sK1 = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
          & X1 = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
     => ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK2)
        & sK2 = X1
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
               => ( X1 = X2
                 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
             => ( X1 = X2
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t66_pre_topc.p',t66_pre_topc)).

fof(f247,plain,
    ( spl9_26
    | ~ spl9_0
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f235,f148,f120,f245])).

fof(f235,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl9_0
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f231,f121])).

fof(f231,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_8 ),
    inference(resolution,[],[f102,f149])).

fof(f196,plain,
    ( spl9_18
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f188,f141,f194])).

fof(f188,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f78,f142])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(cnf_transformation,[],[f62])).

fof(f166,plain,
    ( spl9_12
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f151,f120,f164])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl9_0 ),
    inference(resolution,[],[f88,f121])).

fof(f150,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f77,f148])).

fof(f77,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

fof(f143,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f79,f141])).

fof(f79,plain,(
    sK1 = sK2 ),
    inference(cnf_transformation,[],[f62])).

fof(f122,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f76,f120])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
