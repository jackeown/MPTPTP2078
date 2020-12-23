%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 269 expanded)
%              Number of leaves         :   30 ( 111 expanded)
%              Depth                    :   10
%              Number of atoms          :  418 ( 816 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1180,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f79,f90,f96,f145,f150,f178,f292,f333,f345,f377,f426,f499,f521,f578,f644,f648,f1082,f1147,f1179])).

fof(f1179,plain,
    ( spl15_69
    | ~ spl15_93 ),
    inference(avatar_contradiction_clause,[],[f1178])).

fof(f1178,plain,
    ( $false
    | spl15_69
    | ~ spl15_93 ),
    inference(subsumption_resolution,[],[f1177,f647])).

fof(f647,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | spl15_69 ),
    inference(avatar_component_clause,[],[f646])).

fof(f646,plain,
    ( spl15_69
  <=> m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_69])])).

fof(f1177,plain,
    ( m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ spl15_93 ),
    inference(resolution,[],[f1146,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f1146,plain,
    ( r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ spl15_93 ),
    inference(avatar_component_clause,[],[f1145])).

fof(f1145,plain,
    ( spl15_93
  <=> r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_93])])).

fof(f1147,plain,
    ( spl15_93
    | ~ spl15_16
    | ~ spl15_92 ),
    inference(avatar_split_clause,[],[f1112,f1080,f148,f1145])).

fof(f148,plain,
    ( spl15_16
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f1080,plain,
    ( spl15_92
  <=> r2_hidden(sK11(sK3,sK4,sK5,sK6),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_92])])).

fof(f1112,plain,
    ( r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ spl15_16
    | ~ spl15_92 ),
    inference(resolution,[],[f1081,f152])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(X0,sK1) )
    | ~ spl15_16 ),
    inference(resolution,[],[f149,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f149,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f1081,plain,
    ( r2_hidden(sK11(sK3,sK4,sK5,sK6),k2_relat_1(sK3))
    | ~ spl15_92 ),
    inference(avatar_component_clause,[],[f1080])).

fof(f1082,plain,
    ( spl15_92
    | ~ spl15_68 ),
    inference(avatar_split_clause,[],[f684,f642,f1080])).

fof(f642,plain,
    ( spl15_68
  <=> sP13(sK11(sK3,sK4,sK5,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_68])])).

fof(f684,plain,
    ( r2_hidden(sK11(sK3,sK4,sK5,sK6),k2_relat_1(sK3))
    | ~ spl15_68 ),
    inference(resolution,[],[f643,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ sP13(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ sP13(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f643,plain,
    ( sP13(sK11(sK3,sK4,sK5,sK6),sK3)
    | ~ spl15_68 ),
    inference(avatar_component_clause,[],[f642])).

fof(f648,plain,
    ( ~ spl15_69
    | ~ spl15_41
    | ~ spl15_54
    | ~ spl15_57 ),
    inference(avatar_split_clause,[],[f588,f576,f497,f342,f646])).

fof(f342,plain,
    ( spl15_41
  <=> ! [X7] :
        ( ~ m1_subset_1(X7,sK1)
        | ~ r2_hidden(k4_tarski(X7,sK6),sK4)
        | ~ r2_hidden(k4_tarski(sK5,X7),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_41])])).

fof(f497,plain,
    ( spl15_54
  <=> r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_54])])).

fof(f576,plain,
    ( spl15_57
  <=> r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_57])])).

fof(f588,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ spl15_41
    | ~ spl15_54
    | ~ spl15_57 ),
    inference(subsumption_resolution,[],[f583,f498])).

fof(f498,plain,
    ( r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3)
    | ~ spl15_54 ),
    inference(avatar_component_clause,[],[f497])).

fof(f583,plain,
    ( ~ m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)
    | ~ r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3)
    | ~ spl15_41
    | ~ spl15_57 ),
    inference(resolution,[],[f577,f343])).

fof(f343,plain,
    ( ! [X7] :
        ( ~ r2_hidden(k4_tarski(X7,sK6),sK4)
        | ~ m1_subset_1(X7,sK1)
        | ~ r2_hidden(k4_tarski(sK5,X7),sK3) )
    | ~ spl15_41 ),
    inference(avatar_component_clause,[],[f342])).

fof(f577,plain,
    ( r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4)
    | ~ spl15_57 ),
    inference(avatar_component_clause,[],[f576])).

fof(f644,plain,
    ( spl15_68
    | ~ spl15_54 ),
    inference(avatar_split_clause,[],[f567,f497,f642])).

fof(f567,plain,
    ( sP13(sK11(sK3,sK4,sK5,sK6),sK3)
    | ~ spl15_54 ),
    inference(resolution,[],[f498,f42])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP13(X2,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f578,plain,
    ( spl15_57
    | ~ spl15_45 ),
    inference(avatar_split_clause,[],[f527,f375,f576])).

fof(f375,plain,
    ( spl15_45
  <=> sP10(sK6,sK5,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_45])])).

fof(f527,plain,
    ( r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4)
    | ~ spl15_45 ),
    inference(resolution,[],[f376,f35])).

fof(f35,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP10(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(sK11(X0,X1,X3,X4),X4),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f376,plain,
    ( sP10(sK6,sK5,sK4,sK3)
    | ~ spl15_45 ),
    inference(avatar_component_clause,[],[f375])).

fof(f521,plain,
    ( spl15_45
    | ~ spl15_7
    | ~ spl15_36 ),
    inference(avatar_split_clause,[],[f458,f287,f94,f375])).

fof(f94,plain,
    ( spl15_7
  <=> r2_hidden(k4_tarski(sK5,sK7),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f287,plain,
    ( spl15_36
  <=> r2_hidden(k4_tarski(sK7,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_36])])).

fof(f458,plain,
    ( sP10(sK6,sK5,sK4,sK3)
    | ~ spl15_7
    | ~ spl15_36 ),
    inference(resolution,[],[f379,f288])).

fof(f288,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),sK4)
    | ~ spl15_36 ),
    inference(avatar_component_clause,[],[f287])).

fof(f379,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK7,X0),X1)
        | sP10(X0,sK5,X1,sK3) )
    | ~ spl15_7 ),
    inference(resolution,[],[f95,f33])).

fof(f33,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | sP10(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,
    ( r2_hidden(k4_tarski(sK5,sK7),sK3)
    | ~ spl15_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f499,plain,
    ( spl15_54
    | ~ spl15_45 ),
    inference(avatar_split_clause,[],[f473,f375,f497])).

fof(f473,plain,
    ( r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3)
    | ~ spl15_45 ),
    inference(resolution,[],[f376,f34])).

fof(f34,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP10(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,sK11(X0,X1,X3,X4)),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f426,plain,
    ( ~ spl15_3
    | ~ spl15_6
    | ~ spl15_21
    | spl15_37
    | ~ spl15_45 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | ~ spl15_3
    | ~ spl15_6
    | ~ spl15_21
    | spl15_37
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f344,f424])).

fof(f424,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl15_3
    | ~ spl15_6
    | ~ spl15_21
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f423,f89])).

fof(f89,plain,
    ( v1_relat_1(sK3)
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl15_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f423,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl15_3
    | ~ spl15_21
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f422,f177])).

fof(f177,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl15_21 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl15_21
  <=> v1_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_21])])).

fof(f422,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK3)
    | r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl15_3
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f415,f78])).

fof(f78,plain,
    ( v1_relat_1(sK4)
    | ~ spl15_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl15_3
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f415,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK3)
    | r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl15_45 ),
    inference(resolution,[],[f376,f53])).

fof(f53,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP10(X4,X3,X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ sP10(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f344,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | spl15_37 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl15_37
  <=> r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_37])])).

fof(f377,plain,
    ( spl15_45
    | ~ spl15_3
    | ~ spl15_6
    | ~ spl15_21
    | ~ spl15_37 ),
    inference(avatar_split_clause,[],[f354,f290,f176,f88,f77,f375])).

fof(f354,plain,
    ( sP10(sK6,sK5,sK4,sK3)
    | ~ spl15_3
    | ~ spl15_6
    | ~ spl15_21
    | ~ spl15_37 ),
    inference(subsumption_resolution,[],[f310,f89])).

fof(f310,plain,
    ( sP10(sK6,sK5,sK4,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_3
    | ~ spl15_21
    | ~ spl15_37 ),
    inference(subsumption_resolution,[],[f309,f177])).

fof(f309,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | sP10(sK6,sK5,sK4,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_3
    | ~ spl15_37 ),
    inference(subsumption_resolution,[],[f305,f78])).

fof(f305,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | sP10(sK6,sK5,sK4,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_37 ),
    inference(resolution,[],[f291,f52])).

fof(f52,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | sP10(X4,X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | sP10(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f291,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl15_37 ),
    inference(avatar_component_clause,[],[f290])).

fof(f345,plain,
    ( spl15_41
    | ~ spl15_37
    | ~ spl15_1
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f279,f61,f57,f290,f342])).

fof(f57,plain,
    ( spl15_1
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f61,plain,
    ( spl15_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f279,plain,
    ( ! [X7] :
        ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
        | ~ m1_subset_1(X7,sK1)
        | ~ r2_hidden(k4_tarski(sK5,X7),sK3)
        | ~ r2_hidden(k4_tarski(X7,sK6),sK4) )
    | ~ spl15_1
    | ~ spl15_2 ),
    inference(forward_demodulation,[],[f25,f253])).

fof(f253,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl15_1
    | ~ spl15_2 ),
    inference(resolution,[],[f72,f58])).

fof(f58,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k4_relset_1(sK0,sK1,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) )
    | ~ spl15_2 ),
    inference(resolution,[],[f62,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f62,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f25,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,sK1)
      | ~ r2_hidden(k4_tarski(sK5,X7),sK3)
      | ~ r2_hidden(k4_tarski(X7,sK6),sK4)
      | ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5,X6] :
              ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
            <~> ? [X7] :
                  ( r2_hidden(k4_tarski(X7,X6),X4)
                  & r2_hidden(k4_tarski(X5,X7),X3)
                  & m1_subset_1(X7,X1) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
           => ! [X5,X6] :
                ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
              <=> ? [X7] :
                    ( r2_hidden(k4_tarski(X7,X6),X4)
                    & r2_hidden(k4_tarski(X5,X7),X3)
                    & m1_subset_1(X7,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                       => ! [X5,X6] :
                            ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                          <=> ? [X7] :
                                ( r2_hidden(k4_tarski(X7,X6),X4)
                                & r2_hidden(k4_tarski(X5,X7),X3)
                                & m1_subset_1(X7,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                     => ! [X5,X6] :
                          ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                        <=> ? [X7] :
                              ( r2_hidden(k4_tarski(X7,X6),X4)
                              & r2_hidden(k4_tarski(X5,X7),X3)
                              & m1_subset_1(X7,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relset_1)).

fof(f333,plain,
    ( spl15_37
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f321,f81,f61,f57,f290])).

fof(f81,plain,
    ( spl15_4
  <=> r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f321,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(forward_demodulation,[],[f82,f253])).

fof(f82,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f292,plain,
    ( spl15_36
    | spl15_37
    | ~ spl15_1
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f278,f61,f57,f290,f287])).

fof(f278,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | r2_hidden(k4_tarski(sK7,sK6),sK4)
    | ~ spl15_1
    | ~ spl15_2 ),
    inference(forward_demodulation,[],[f28,f253])).

fof(f28,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),sK4)
    | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f14])).

fof(f178,plain,
    ( spl15_21
    | ~ spl15_3
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f168,f88,f77,f176])).

fof(f168,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl15_3
    | ~ spl15_6 ),
    inference(resolution,[],[f98,f78])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k5_relat_1(sK3,X0)) )
    | ~ spl15_6 ),
    inference(resolution,[],[f89,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f150,plain,
    ( spl15_16
    | ~ spl15_2
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f146,f143,f61,f148])).

fof(f143,plain,
    ( spl15_15
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f146,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl15_2
    | ~ spl15_15 ),
    inference(forward_demodulation,[],[f144,f71])).

fof(f71,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl15_2 ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f144,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl15_15 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( spl15_15
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f70,f61,f143])).

fof(f70,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl15_2 ),
    inference(resolution,[],[f62,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f96,plain,
    ( spl15_4
    | spl15_7 ),
    inference(avatar_split_clause,[],[f27,f94,f81])).

fof(f27,plain,
    ( r2_hidden(k4_tarski(sK5,sK7),sK3)
    | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f14])).

fof(f90,plain,
    ( spl15_6
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f75,f61,f88])).

fof(f75,plain,
    ( v1_relat_1(sK3)
    | ~ spl15_2 ),
    inference(subsumption_resolution,[],[f73,f48])).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f73,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl15_2 ),
    inference(resolution,[],[f62,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f79,plain,
    ( spl15_3
    | ~ spl15_1 ),
    inference(avatar_split_clause,[],[f69,f57,f77])).

fof(f69,plain,
    ( v1_relat_1(sK4)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f67,f48])).

fof(f67,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4)
    | ~ spl15_1 ),
    inference(resolution,[],[f58,f47])).

fof(f63,plain,(
    spl15_2 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    spl15_1 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (19102)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.46  % (19105)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (19103)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (19120)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (19108)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (19101)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (19099)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (19109)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (19114)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (19115)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (19117)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (19118)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (19119)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (19116)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (19100)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (19106)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (19104)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (19112)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (19110)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (19111)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.54  % (19113)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.54  % (19099)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f1180,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f59,f63,f79,f90,f96,f145,f150,f178,f292,f333,f345,f377,f426,f499,f521,f578,f644,f648,f1082,f1147,f1179])).
% 0.20/0.54  fof(f1179,plain,(
% 0.20/0.54    spl15_69 | ~spl15_93),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1178])).
% 0.20/0.54  fof(f1178,plain,(
% 0.20/0.54    $false | (spl15_69 | ~spl15_93)),
% 0.20/0.54    inference(subsumption_resolution,[],[f1177,f647])).
% 0.20/0.54  fof(f647,plain,(
% 0.20/0.54    ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | spl15_69),
% 0.20/0.54    inference(avatar_component_clause,[],[f646])).
% 0.20/0.54  fof(f646,plain,(
% 0.20/0.54    spl15_69 <=> m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_69])])).
% 0.20/0.54  fof(f1177,plain,(
% 0.20/0.54    m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~spl15_93),
% 0.20/0.54    inference(resolution,[],[f1146,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.54  fof(f1146,plain,(
% 0.20/0.54    r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1) | ~spl15_93),
% 0.20/0.54    inference(avatar_component_clause,[],[f1145])).
% 0.20/0.54  fof(f1145,plain,(
% 0.20/0.54    spl15_93 <=> r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_93])])).
% 0.20/0.54  fof(f1147,plain,(
% 0.20/0.54    spl15_93 | ~spl15_16 | ~spl15_92),
% 0.20/0.54    inference(avatar_split_clause,[],[f1112,f1080,f148,f1145])).
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    spl15_16 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).
% 0.20/0.54  fof(f1080,plain,(
% 0.20/0.54    spl15_92 <=> r2_hidden(sK11(sK3,sK4,sK5,sK6),k2_relat_1(sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_92])])).
% 0.20/0.54  fof(f1112,plain,(
% 0.20/0.54    r2_hidden(sK11(sK3,sK4,sK5,sK6),sK1) | (~spl15_16 | ~spl15_92)),
% 0.20/0.54    inference(resolution,[],[f1081,f152])).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(X0,sK1)) ) | ~spl15_16),
% 0.20/0.54    inference(resolution,[],[f149,f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl15_16),
% 0.20/0.54    inference(avatar_component_clause,[],[f148])).
% 0.20/0.54  fof(f1081,plain,(
% 0.20/0.54    r2_hidden(sK11(sK3,sK4,sK5,sK6),k2_relat_1(sK3)) | ~spl15_92),
% 0.20/0.54    inference(avatar_component_clause,[],[f1080])).
% 0.20/0.54  fof(f1082,plain,(
% 0.20/0.54    spl15_92 | ~spl15_68),
% 0.20/0.54    inference(avatar_split_clause,[],[f684,f642,f1080])).
% 0.20/0.54  fof(f642,plain,(
% 0.20/0.54    spl15_68 <=> sP13(sK11(sK3,sK4,sK5,sK6),sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_68])])).
% 0.20/0.54  fof(f684,plain,(
% 0.20/0.54    r2_hidden(sK11(sK3,sK4,sK5,sK6),k2_relat_1(sK3)) | ~spl15_68),
% 0.20/0.54    inference(resolution,[],[f643,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X2,X0] : (~sP13(X2,X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.54    inference(equality_resolution,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~sP13(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.54  fof(f643,plain,(
% 0.20/0.54    sP13(sK11(sK3,sK4,sK5,sK6),sK3) | ~spl15_68),
% 0.20/0.54    inference(avatar_component_clause,[],[f642])).
% 0.20/0.54  fof(f648,plain,(
% 0.20/0.54    ~spl15_69 | ~spl15_41 | ~spl15_54 | ~spl15_57),
% 0.20/0.54    inference(avatar_split_clause,[],[f588,f576,f497,f342,f646])).
% 0.20/0.54  fof(f342,plain,(
% 0.20/0.54    spl15_41 <=> ! [X7] : (~m1_subset_1(X7,sK1) | ~r2_hidden(k4_tarski(X7,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,X7),sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_41])])).
% 0.20/0.54  fof(f497,plain,(
% 0.20/0.54    spl15_54 <=> r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_54])])).
% 0.20/0.54  fof(f576,plain,(
% 0.20/0.54    spl15_57 <=> r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_57])])).
% 0.20/0.54  fof(f588,plain,(
% 0.20/0.54    ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | (~spl15_41 | ~spl15_54 | ~spl15_57)),
% 0.20/0.54    inference(subsumption_resolution,[],[f583,f498])).
% 0.20/0.54  fof(f498,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3) | ~spl15_54),
% 0.20/0.54    inference(avatar_component_clause,[],[f497])).
% 0.20/0.54  fof(f583,plain,(
% 0.20/0.54    ~m1_subset_1(sK11(sK3,sK4,sK5,sK6),sK1) | ~r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3) | (~spl15_41 | ~spl15_57)),
% 0.20/0.54    inference(resolution,[],[f577,f343])).
% 0.20/0.54  fof(f343,plain,(
% 0.20/0.54    ( ! [X7] : (~r2_hidden(k4_tarski(X7,sK6),sK4) | ~m1_subset_1(X7,sK1) | ~r2_hidden(k4_tarski(sK5,X7),sK3)) ) | ~spl15_41),
% 0.20/0.54    inference(avatar_component_clause,[],[f342])).
% 0.20/0.54  fof(f577,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4) | ~spl15_57),
% 0.20/0.54    inference(avatar_component_clause,[],[f576])).
% 0.20/0.54  fof(f644,plain,(
% 0.20/0.54    spl15_68 | ~spl15_54),
% 0.20/0.54    inference(avatar_split_clause,[],[f567,f497,f642])).
% 0.20/0.54  fof(f567,plain,(
% 0.20/0.54    sP13(sK11(sK3,sK4,sK5,sK6),sK3) | ~spl15_54),
% 0.20/0.54    inference(resolution,[],[f498,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | sP13(X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f578,plain,(
% 0.20/0.54    spl15_57 | ~spl15_45),
% 0.20/0.54    inference(avatar_split_clause,[],[f527,f375,f576])).
% 0.20/0.54  fof(f375,plain,(
% 0.20/0.54    spl15_45 <=> sP10(sK6,sK5,sK4,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_45])])).
% 0.20/0.54  fof(f527,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK11(sK3,sK4,sK5,sK6),sK6),sK4) | ~spl15_45),
% 0.20/0.54    inference(resolution,[],[f376,f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X4,X0,X3,X1] : (~sP10(X4,X3,X1,X0) | r2_hidden(k4_tarski(sK11(X0,X1,X3,X4),X4),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.20/0.54  fof(f376,plain,(
% 0.20/0.54    sP10(sK6,sK5,sK4,sK3) | ~spl15_45),
% 0.20/0.54    inference(avatar_component_clause,[],[f375])).
% 0.20/0.54  fof(f521,plain,(
% 0.20/0.54    spl15_45 | ~spl15_7 | ~spl15_36),
% 0.20/0.54    inference(avatar_split_clause,[],[f458,f287,f94,f375])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    spl15_7 <=> r2_hidden(k4_tarski(sK5,sK7),sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).
% 0.20/0.54  fof(f287,plain,(
% 0.20/0.54    spl15_36 <=> r2_hidden(k4_tarski(sK7,sK6),sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_36])])).
% 0.20/0.54  fof(f458,plain,(
% 0.20/0.54    sP10(sK6,sK5,sK4,sK3) | (~spl15_7 | ~spl15_36)),
% 0.20/0.54    inference(resolution,[],[f379,f288])).
% 0.20/0.54  fof(f288,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK7,sK6),sK4) | ~spl15_36),
% 0.20/0.54    inference(avatar_component_clause,[],[f287])).
% 0.20/0.54  fof(f379,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK7,X0),X1) | sP10(X0,sK5,X1,sK3)) ) | ~spl15_7),
% 0.20/0.54    inference(resolution,[],[f95,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(k4_tarski(X3,X5),X0) | ~r2_hidden(k4_tarski(X5,X4),X1) | sP10(X4,X3,X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK5,sK7),sK3) | ~spl15_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f94])).
% 0.20/0.54  fof(f499,plain,(
% 0.20/0.54    spl15_54 | ~spl15_45),
% 0.20/0.54    inference(avatar_split_clause,[],[f473,f375,f497])).
% 0.20/0.54  fof(f473,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK5,sK11(sK3,sK4,sK5,sK6)),sK3) | ~spl15_45),
% 0.20/0.54    inference(resolution,[],[f376,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X4,X0,X3,X1] : (~sP10(X4,X3,X1,X0) | r2_hidden(k4_tarski(X3,sK11(X0,X1,X3,X4)),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f426,plain,(
% 0.20/0.54    ~spl15_3 | ~spl15_6 | ~spl15_21 | spl15_37 | ~spl15_45),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f425])).
% 0.20/0.54  fof(f425,plain,(
% 0.20/0.54    $false | (~spl15_3 | ~spl15_6 | ~spl15_21 | spl15_37 | ~spl15_45)),
% 0.20/0.54    inference(subsumption_resolution,[],[f344,f424])).
% 0.20/0.54  fof(f424,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | (~spl15_3 | ~spl15_6 | ~spl15_21 | ~spl15_45)),
% 0.20/0.54    inference(subsumption_resolution,[],[f423,f89])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    v1_relat_1(sK3) | ~spl15_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    spl15_6 <=> v1_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).
% 0.20/0.54  fof(f423,plain,(
% 0.20/0.54    ~v1_relat_1(sK3) | r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | (~spl15_3 | ~spl15_21 | ~spl15_45)),
% 0.20/0.54    inference(subsumption_resolution,[],[f422,f177])).
% 0.20/0.54  fof(f177,plain,(
% 0.20/0.54    v1_relat_1(k5_relat_1(sK3,sK4)) | ~spl15_21),
% 0.20/0.54    inference(avatar_component_clause,[],[f176])).
% 0.20/0.54  fof(f176,plain,(
% 0.20/0.54    spl15_21 <=> v1_relat_1(k5_relat_1(sK3,sK4))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_21])])).
% 0.20/0.54  fof(f422,plain,(
% 0.20/0.54    ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK3) | r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | (~spl15_3 | ~spl15_45)),
% 0.20/0.54    inference(subsumption_resolution,[],[f415,f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    v1_relat_1(sK4) | ~spl15_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f77])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    spl15_3 <=> v1_relat_1(sK4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).
% 0.20/0.54  fof(f415,plain,(
% 0.20/0.54    ~v1_relat_1(sK4) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | ~v1_relat_1(sK3) | r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~spl15_45),
% 0.20/0.54    inference(resolution,[],[f376,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X4,X0,X3,X1] : (~sP10(X4,X3,X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 0.20/0.54    inference(equality_resolution,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~sP10(X4,X3,X1,X0) | r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f344,plain,(
% 0.20/0.54    ~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | spl15_37),
% 0.20/0.54    inference(avatar_component_clause,[],[f290])).
% 0.20/0.54  fof(f290,plain,(
% 0.20/0.54    spl15_37 <=> r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_37])])).
% 0.20/0.54  fof(f377,plain,(
% 0.20/0.54    spl15_45 | ~spl15_3 | ~spl15_6 | ~spl15_21 | ~spl15_37),
% 0.20/0.54    inference(avatar_split_clause,[],[f354,f290,f176,f88,f77,f375])).
% 0.20/0.54  fof(f354,plain,(
% 0.20/0.54    sP10(sK6,sK5,sK4,sK3) | (~spl15_3 | ~spl15_6 | ~spl15_21 | ~spl15_37)),
% 0.20/0.54    inference(subsumption_resolution,[],[f310,f89])).
% 0.20/0.54  fof(f310,plain,(
% 0.20/0.54    sP10(sK6,sK5,sK4,sK3) | ~v1_relat_1(sK3) | (~spl15_3 | ~spl15_21 | ~spl15_37)),
% 0.20/0.54    inference(subsumption_resolution,[],[f309,f177])).
% 0.20/0.54  fof(f309,plain,(
% 0.20/0.54    ~v1_relat_1(k5_relat_1(sK3,sK4)) | sP10(sK6,sK5,sK4,sK3) | ~v1_relat_1(sK3) | (~spl15_3 | ~spl15_37)),
% 0.20/0.54    inference(subsumption_resolution,[],[f305,f78])).
% 0.20/0.54  fof(f305,plain,(
% 0.20/0.54    ~v1_relat_1(sK4) | ~v1_relat_1(k5_relat_1(sK3,sK4)) | sP10(sK6,sK5,sK4,sK3) | ~v1_relat_1(sK3) | ~spl15_37),
% 0.20/0.54    inference(resolution,[],[f291,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | sP10(X4,X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | sP10(X4,X3,X1,X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f291,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~spl15_37),
% 0.20/0.54    inference(avatar_component_clause,[],[f290])).
% 0.20/0.54  fof(f345,plain,(
% 0.20/0.54    spl15_41 | ~spl15_37 | ~spl15_1 | ~spl15_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f279,f61,f57,f290,f342])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    spl15_1 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    spl15_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).
% 0.20/0.54  fof(f279,plain,(
% 0.20/0.54    ( ! [X7] : (~r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | ~m1_subset_1(X7,sK1) | ~r2_hidden(k4_tarski(sK5,X7),sK3) | ~r2_hidden(k4_tarski(X7,sK6),sK4)) ) | (~spl15_1 | ~spl15_2)),
% 0.20/0.54    inference(forward_demodulation,[],[f25,f253])).
% 0.20/0.54  fof(f253,plain,(
% 0.20/0.54    k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl15_1 | ~spl15_2)),
% 0.20/0.54    inference(resolution,[],[f72,f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl15_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f57])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k4_relset_1(sK0,sK1,X1,X2,sK3,X0) = k5_relat_1(sK3,X0)) ) | ~spl15_2),
% 0.20/0.54    inference(resolution,[],[f62,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl15_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f61])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ( ! [X7] : (~m1_subset_1(X7,sK1) | ~r2_hidden(k4_tarski(sK5,X7),sK3) | ~r2_hidden(k4_tarski(X7,sK6),sK4) | ~r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (? [X4] : (? [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <~> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1)))))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.54  fof(f12,negated_conjecture,(
% 0.20/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))))))))),
% 0.20/0.54    inference(negated_conjecture,[],[f11])).
% 0.20/0.54  fof(f11,conjecture,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ! [X5,X6] : (r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4)) <=> ? [X7] : (r2_hidden(k4_tarski(X7,X6),X4) & r2_hidden(k4_tarski(X5,X7),X3) & m1_subset_1(X7,X1))))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relset_1)).
% 0.20/0.54  fof(f333,plain,(
% 0.20/0.54    spl15_37 | ~spl15_1 | ~spl15_2 | ~spl15_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f321,f81,f61,f57,f290])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    spl15_4 <=> r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).
% 0.20/0.54  fof(f321,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | (~spl15_1 | ~spl15_2 | ~spl15_4)),
% 0.20/0.54    inference(forward_demodulation,[],[f82,f253])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) | ~spl15_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f81])).
% 0.20/0.54  fof(f292,plain,(
% 0.20/0.54    spl15_36 | spl15_37 | ~spl15_1 | ~spl15_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f278,f61,f57,f290,f287])).
% 0.20/0.54  fof(f278,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) | r2_hidden(k4_tarski(sK7,sK6),sK4) | (~spl15_1 | ~spl15_2)),
% 0.20/0.54    inference(forward_demodulation,[],[f28,f253])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK7,sK6),sK4) | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f178,plain,(
% 0.20/0.54    spl15_21 | ~spl15_3 | ~spl15_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f168,f88,f77,f176])).
% 0.20/0.54  fof(f168,plain,(
% 0.20/0.54    v1_relat_1(k5_relat_1(sK3,sK4)) | (~spl15_3 | ~spl15_6)),
% 0.20/0.54    inference(resolution,[],[f98,f78])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(sK3,X0))) ) | ~spl15_6),
% 0.20/0.54    inference(resolution,[],[f89,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    spl15_16 | ~spl15_2 | ~spl15_15),
% 0.20/0.54    inference(avatar_split_clause,[],[f146,f143,f61,f148])).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    spl15_15 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).
% 0.20/0.54  fof(f146,plain,(
% 0.20/0.54    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | (~spl15_2 | ~spl15_15)),
% 0.20/0.54    inference(forward_demodulation,[],[f144,f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl15_2),
% 0.20/0.54    inference(resolution,[],[f62,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.54  fof(f144,plain,(
% 0.20/0.54    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) | ~spl15_15),
% 0.20/0.54    inference(avatar_component_clause,[],[f143])).
% 0.20/0.54  fof(f145,plain,(
% 0.20/0.54    spl15_15 | ~spl15_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f70,f61,f143])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) | ~spl15_2),
% 0.20/0.54    inference(resolution,[],[f62,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    spl15_4 | spl15_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f27,f94,f81])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    r2_hidden(k4_tarski(sK5,sK7),sK3) | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    spl15_6 | ~spl15_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f75,f61,f88])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    v1_relat_1(sK3) | ~spl15_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f73,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl15_2),
% 0.20/0.54    inference(resolution,[],[f62,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    spl15_3 | ~spl15_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f69,f57,f77])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    v1_relat_1(sK4) | ~spl15_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f67,f48])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK4) | ~spl15_1),
% 0.20/0.54    inference(resolution,[],[f58,f47])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    spl15_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f30,f61])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    spl15_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f29,f57])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (19099)------------------------------
% 0.20/0.54  % (19099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19099)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (19099)Memory used [KB]: 7547
% 0.20/0.54  % (19099)Time elapsed: 0.143 s
% 0.20/0.54  % (19099)------------------------------
% 0.20/0.54  % (19099)------------------------------
% 0.20/0.54  % (19096)Success in time 0.189 s
%------------------------------------------------------------------------------
