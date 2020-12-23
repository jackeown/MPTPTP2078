%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t58_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:41 EDT 2019

% Result     : Theorem 26.52s
% Output     : Refutation 26.52s
% Verified   : 
% Statistics : Number of formulae       : 1455 (8117 expanded)
%              Number of leaves         :  409 (3002 expanded)
%              Depth                    :   17
%              Number of atoms          : 6904 (34537 expanded)
%              Number of equality atoms :   10 ( 913 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :   11 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17542,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f134,f141,f148,f155,f162,f169,f176,f183,f190,f197,f204,f211,f218,f225,f236,f243,f250,f257,f268,f275,f293,f306,f319,f320,f331,f338,f355,f365,f379,f380,f388,f393,f409,f422,f432,f489,f501,f513,f521,f526,f528,f562,f576,f689,f694,f698,f699,f700,f701,f709,f1006,f1010,f1035,f1042,f1077,f1084,f1166,f1170,f1976,f1980,f1984,f2038,f2043,f2056,f2135,f2632,f2641,f2701,f2705,f2737,f2744,f2834,f2841,f2938,f2942,f3043,f3047,f3080,f3087,f3120,f3127,f3219,f3223,f3255,f3259,f3292,f3299,f3332,f3339,f3369,f3373,f3432,f3436,f3478,f3485,f3518,f3525,f3555,f3559,f3618,f3622,f3655,f3662,f3695,f3702,f3732,f3736,f4001,f4005,f4038,f4045,f4087,f4094,f4124,f4128,f4160,f4164,f4197,f4204,f4237,f4244,f4274,f4278,f4310,f4314,f4347,f4354,f4391,f4398,f4428,f4432,f4464,f4468,f4501,f4508,f4541,f4548,f4578,f4582,f4678,f4688,f4696,f5059,f5090,f5094,f5170,f5174,f5217,f5429,f5433,f5470,f5526,f5672,f5676,f5705,f5718,f5737,f5756,f5781,f5786,f5814,f5827,f5846,f5865,f5890,f5895,f5909,f5945,f6047,f6051,f6925,f6929,f7449,f7453,f7654,f7658,f7939,f7943,f8260,f8264,f8560,f8564,f8600,f8604,f8640,f8644,f8649,f8653,f8660,f8667,f8671,f8675,f8676,f8677,f8691,f8695,f8702,f8709,f8713,f8714,f8715,f8728,f8747,f8760,f8773,f8780,f8793,f8830,f8834,f8839,f8844,f8848,f8855,f8862,f8866,f8870,f8871,f8872,f8873,f8907,f8914,f8927,f8940,f8957,f8972,f8987,f9144,f9148,f9222,f9226,f10344,f10348,f10533,f10537,f10736,f10740,f11132,f11136,f11253,f11257,f11429,f11433,f11550,f11554,f11726,f11730,f11869,f11873,f12025,f12029,f12146,f12150,f12305,f12309,f12426,f12430,f12617,f12621,f12740,f12744,f12901,f12905,f13025,f13029,f13201,f13205,f13322,f13326,f15335,f15339,f15343,f15347,f15351,f15355,f15359,f15363,f15370,f15374,f15377,f15527,f15531,f15535,f15539,f15543,f15547,f15551,f15555,f15559,f15563,f15567,f15571,f15575,f15579,f15583,f15587,f15591,f15595,f15599,f15603,f15607,f15611,f15615,f15619,f15623,f17100,f17104,f17270,f17394,f17396,f17436,f17440,f17447,f17451,f17455,f17459,f17463,f17467,f17471,f17475,f17479,f17483,f17487,f17491,f17495,f17499,f17540,f17541])).

fof(f17541,plain,
    ( ~ spl9_659
    | spl9_661 ),
    inference(avatar_split_clause,[],[f17539,f17392,f17386])).

fof(f17386,plain,
    ( spl9_659
  <=> ~ r1_tarski(k5_relat_1(sK3,sK4),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_659])])).

fof(f17392,plain,
    ( spl9_661
  <=> ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_661])])).

fof(f17539,plain,
    ( ~ r1_tarski(k5_relat_1(sK3,sK4),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl9_661 ),
    inference(resolution,[],[f17393,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t3_subset)).

fof(f17393,plain,
    ( ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl9_661 ),
    inference(avatar_component_clause,[],[f17392])).

fof(f17540,plain,
    ( ~ spl9_17
    | spl9_582
    | ~ spl9_11
    | spl9_578
    | spl9_661 ),
    inference(avatar_split_clause,[],[f17538,f17392,f15324,f157,f15333,f178])).

fof(f178,plain,
    ( spl9_17
  <=> ~ v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f15333,plain,
    ( spl9_582
  <=> ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_582])])).

fof(f157,plain,
    ( spl9_11
  <=> ~ v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f15324,plain,
    ( spl9_578
  <=> ! [X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_578])])).

fof(f17538,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl9_661 ),
    inference(resolution,[],[f17393,f833])).

fof(f833,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f832])).

fof(f832,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f118,f116])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',redefinition_k1_partfun1)).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',dt_k1_partfun1)).

fof(f17499,plain,
    ( spl9_78
    | spl9_692
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f2627,f167,f17497,f481])).

fof(f481,plain,
    ( spl9_78
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f17497,plain,
    ( spl9_692
  <=> ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK3,X0))
        | r2_hidden(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK3,X0)))))),u1_struct_0(sK0))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK3,X0))))
        | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK3,X0)))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_692])])).

fof(f167,plain,
    ( spl9_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f2627,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK3,X0))
        | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK3,X0))))))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK3,X0))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK3,X0)))))),u1_struct_0(sK0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f1303,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t2_subset)).

fof(f1303,plain,
    ( ! [X11] :
        ( m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK3,X11)))))),u1_struct_0(sK0))
        | v1_xboole_0(k10_relat_1(sK3,X11))
        | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK3,X11))))))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK3,X11)))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f846,f478])).

fof(f478,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(sK3,X1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f474,f370])).

fof(f370,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f110,f106])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t4_subset)).

fof(f474,plain,
    ( ! [X10] : r1_tarski(k10_relat_1(sK3,X10),u1_struct_0(sK0))
    | ~ spl9_12 ),
    inference(resolution,[],[f471,f168])).

fof(f168,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f471,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k10_relat_1(X2,X3),X0) ) ),
    inference(duplicate_literal_removal,[],[f468])).

fof(f468,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k10_relat_1(X2,X3),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f460,f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',redefinition_k8_relset_1)).

fof(f460,plain,(
    ! [X12,X10,X13,X11] :
      ( r1_tarski(k8_relset_1(X11,X12,X10,X13),X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ),
    inference(resolution,[],[f112,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',dt_k8_relset_1)).

fof(f846,plain,(
    ! [X34] :
      ( r2_hidden(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X34))))),X34)
      | v1_xboole_0(sK6(k1_zfmisc_1(X34)))
      | v1_xboole_0(X34)
      | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X34))))) ) ),
    inference(resolution,[],[f455,f103])).

fof(f455,plain,(
    ! [X3] :
      ( m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X3))))),X3)
      | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X3)))))
      | v1_xboole_0(sK6(k1_zfmisc_1(X3))) ) ),
    inference(resolution,[],[f445,f373])).

fof(f373,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK6(k1_zfmisc_1(X6)))
      | m1_subset_1(X5,X6) ) ),
    inference(resolution,[],[f110,f99])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',existence_m1_subset_1)).

fof(f445,plain,(
    ! [X7] :
      ( r2_hidden(sK6(sK6(k1_zfmisc_1(X7))),X7)
      | v1_xboole_0(X7)
      | v1_xboole_0(sK6(k1_zfmisc_1(X7))) ) ),
    inference(resolution,[],[f374,f103])).

fof(f374,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK6(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK6(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f373,f280])).

fof(f280,plain,(
    ! [X2] :
      ( r2_hidden(sK6(X2),X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f103,f99])).

fof(f17495,plain,
    ( spl9_78
    | spl9_690
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f2636,f167,f17493,f481])).

fof(f17493,plain,
    ( spl9_690
  <=> ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK3,X0))
        | r2_hidden(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK3,X0)))))),u1_struct_0(sK0))
        | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK3,X0))))))
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK3,X0))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_690])])).

fof(f2636,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK3,X0))
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK3,X0)))))
        | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK3,X0))))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK3,X0)))))),u1_struct_0(sK0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f1687,f103])).

fof(f1687,plain,
    ( ! [X11] :
        ( m1_subset_1(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK3,X11)))))),u1_struct_0(sK0))
        | v1_xboole_0(k10_relat_1(sK3,X11))
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK3,X11)))))
        | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK3,X11)))))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f959,f478])).

fof(f959,plain,(
    ! [X39] :
      ( r2_hidden(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(X39))))),X39)
      | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(X39)))))
      | v1_xboole_0(X39)
      | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(X39)))) ) ),
    inference(resolution,[],[f661,f103])).

fof(f661,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(X0))))),X0)
      | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(X0))))
      | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(X0))))) ) ),
    inference(resolution,[],[f441,f280])).

fof(f441,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(X0)))))
      | m1_subset_1(X1,X0)
      | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(X0)))) ) ),
    inference(resolution,[],[f374,f110])).

fof(f17491,plain,
    ( ~ spl9_53
    | spl9_688
    | ~ spl9_296 ),
    inference(avatar_split_clause,[],[f5096,f5088,f17489,f326])).

fof(f326,plain,
    ( spl9_53
  <=> ~ v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f17489,plain,
    ( spl9_688
  <=> ! [X0] : v1_xboole_0(k10_relat_1(sK3,k10_relat_1(sK3,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_688])])).

fof(f5088,plain,
    ( spl9_296
  <=> ! [X138] : v1_xboole_0(k10_relat_1(k5_relat_1(sK3,sK3),X138)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_296])])).

fof(f5096,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK3,k10_relat_1(sK3,X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl9_296 ),
    inference(duplicate_literal_removal,[],[f5095])).

fof(f5095,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK3,k10_relat_1(sK3,X0)))
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl9_296 ),
    inference(superposition,[],[f5089,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t181_relat_1)).

fof(f5089,plain,
    ( ! [X138] : v1_xboole_0(k10_relat_1(k5_relat_1(sK3,sK3),X138))
    | ~ spl9_296 ),
    inference(avatar_component_clause,[],[f5088])).

fof(f17487,plain,
    ( ~ spl9_53
    | ~ spl9_55
    | spl9_686
    | ~ spl9_298 ),
    inference(avatar_split_clause,[],[f5097,f5092,f17485,f333,f326])).

fof(f333,plain,
    ( spl9_55
  <=> ~ v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f17485,plain,
    ( spl9_686
  <=> ! [X0] : v1_xboole_0(k10_relat_1(sK3,k10_relat_1(sK4,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_686])])).

fof(f5092,plain,
    ( spl9_298
  <=> ! [X139] : v1_xboole_0(k10_relat_1(k5_relat_1(sK3,sK4),X139)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_298])])).

fof(f5097,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK3,k10_relat_1(sK4,X0)))
        | ~ v1_relat_1(sK4)
        | ~ v1_relat_1(sK3) )
    | ~ spl9_298 ),
    inference(superposition,[],[f5093,f100])).

fof(f5093,plain,
    ( ! [X139] : v1_xboole_0(k10_relat_1(k5_relat_1(sK3,sK4),X139))
    | ~ spl9_298 ),
    inference(avatar_component_clause,[],[f5092])).

fof(f17483,plain,
    ( spl9_78
    | spl9_684
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f15378,f167,f17481,f481])).

fof(f17481,plain,
    ( spl9_684
  <=> ! [X1,X3,X0,X2,X4] :
        ( v1_xboole_0(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X0),X1),X2))),X3),X4))
        | r2_hidden(sK6(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X0),X1),X2))),X3),X4)),u1_struct_0(sK0))
        | v1_xboole_0(k10_relat_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_684])])).

fof(f15378,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v1_xboole_0(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X0),X1),X2))),X3),X4))
        | v1_xboole_0(k10_relat_1(sK3,X0))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK6(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X0),X1),X2))),X3),X4)),u1_struct_0(sK0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f1811,f103])).

fof(f1811,plain,
    ( ! [X6,X10,X8,X7,X9] :
        ( m1_subset_1(sK6(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X6),X7),X8))),X9),X10)),u1_struct_0(sK0))
        | v1_xboole_0(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X6),X7),X8))),X9),X10))
        | v1_xboole_0(k10_relat_1(sK3,X6)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f1783,f476])).

fof(f476,plain,(
    ! [X14,X12,X13] : r1_tarski(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X14),X12) ),
    inference(resolution,[],[f471,f99])).

fof(f1783,plain,
    ( ! [X28,X26,X29,X27] :
        ( ~ r1_tarski(X26,k2_zfmisc_1(k10_relat_1(sK3,X28),X29))
        | v1_xboole_0(k10_relat_1(sK3,X28))
        | v1_xboole_0(k10_relat_1(X26,X27))
        | m1_subset_1(sK6(k10_relat_1(X26,X27)),u1_struct_0(sK0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f1754,f478])).

fof(f1754,plain,(
    ! [X202,X200,X203,X201] :
      ( r2_hidden(sK6(k10_relat_1(X200,X203)),X201)
      | v1_xboole_0(k10_relat_1(X200,X203))
      | v1_xboole_0(X201)
      | ~ r1_tarski(X200,k2_zfmisc_1(X201,X202)) ) ),
    inference(resolution,[],[f1722,f103])).

fof(f1722,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(k10_relat_1(X0,X1)),X2)
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,X3))
      | v1_xboole_0(k10_relat_1(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f1702])).

fof(f1702,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(k10_relat_1(X0,X1)),X2)
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,X3))
      | v1_xboole_0(k10_relat_1(X0,X1))
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f1283,f106])).

fof(f1283,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(sK6(k10_relat_1(X2,X3)),X0)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | v1_xboole_0(k10_relat_1(X2,X3)) ) ),
    inference(superposition,[],[f1261,f113])).

fof(f1261,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(k8_relset_1(X2,X3,X0,X1))
      | m1_subset_1(sK6(k10_relat_1(X0,X1)),X2)
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f1260,f106])).

fof(f1260,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(sK6(k10_relat_1(X2,X3)),X0)
      | v1_xboole_0(k8_relset_1(X0,X1,X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f1259])).

fof(f1259,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(k10_relat_1(X2,X3)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k8_relset_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f716,f113])).

fof(f716,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(k8_relset_1(X0,X1,X2,X3)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k8_relset_1(X0,X1,X2,X3)) ) ),
    inference(resolution,[],[f458,f280])).

fof(f458,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k8_relset_1(X1,X2,X0,X4))
      | m1_subset_1(X3,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f112,f110])).

fof(f17479,plain,
    ( spl9_78
    | spl9_682
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f2123,f167,f17477,f481])).

fof(f17477,plain,
    ( spl9_682
  <=> ! [X90] :
        ( v1_xboole_0(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X90))
        | r2_hidden(sK6(k10_relat_1(sK3,X90)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_682])])).

fof(f2123,plain,
    ( ! [X90] :
        ( v1_xboole_0(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X90))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK6(k10_relat_1(sK3,X90)),u1_struct_0(sK0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f2109,f168])).

fof(f2109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k8_relset_1(X0,X1,X2,X3))
      | v1_xboole_0(X0)
      | r2_hidden(sK6(k10_relat_1(X2,X3)),X0) ) ),
    inference(duplicate_literal_removal,[],[f2108])).

fof(f2108,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(k10_relat_1(X2,X3)),X0)
      | v1_xboole_0(k8_relset_1(X0,X1,X2,X3))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f1258,f113])).

fof(f1258,plain,(
    ! [X118,X120,X119,X117] :
      ( r2_hidden(sK6(k8_relset_1(X118,X119,X117,X120)),X118)
      | v1_xboole_0(k8_relset_1(X118,X119,X117,X120))
      | v1_xboole_0(X118)
      | ~ m1_subset_1(X117,k1_zfmisc_1(k2_zfmisc_1(X118,X119))) ) ),
    inference(resolution,[],[f716,f103])).

fof(f17475,plain,
    ( spl9_680
    | ~ spl9_79
    | ~ spl9_53
    | ~ spl9_55
    | ~ spl9_658 ),
    inference(avatar_split_clause,[],[f17398,f17383,f333,f326,f484,f17473])).

fof(f17473,plain,
    ( spl9_680
  <=> ! [X3,X2] : ~ r2_hidden(X2,k10_relat_1(sK3,k10_relat_1(sK4,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_680])])).

fof(f484,plain,
    ( spl9_79
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).

fof(f17383,plain,
    ( spl9_658
  <=> r1_tarski(k5_relat_1(sK3,sK4),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_658])])).

fof(f17398,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK4)
        | ~ v1_relat_1(sK3)
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ r2_hidden(X2,k10_relat_1(sK3,k10_relat_1(sK4,X3))) )
    | ~ spl9_658 ),
    inference(resolution,[],[f17384,f927])).

fof(f927,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( ~ r1_tarski(k5_relat_1(X6,X7),k2_zfmisc_1(X8,X9))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | ~ v1_xboole_0(X8)
      | ~ r2_hidden(X10,k10_relat_1(X6,k10_relat_1(X7,X11))) ) ),
    inference(resolution,[],[f591,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t5_subset)).

fof(f591,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_relat_1(X0,k10_relat_1(X1,X2)),k1_zfmisc_1(X3))
      | ~ r1_tarski(k5_relat_1(X0,X1),k2_zfmisc_1(X3,X4))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f543,f100])).

fof(f543,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k10_relat_1(X0,X1),k1_zfmisc_1(X2))
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f470,f106])).

fof(f470,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | m1_subset_1(k10_relat_1(X6,X7),k1_zfmisc_1(X4)) ) ),
    inference(duplicate_literal_removal,[],[f469])).

fof(f469,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k10_relat_1(X6,X7),k1_zfmisc_1(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(superposition,[],[f112,f113])).

fof(f17384,plain,
    ( r1_tarski(k5_relat_1(sK3,sK4),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl9_658 ),
    inference(avatar_component_clause,[],[f17383])).

fof(f17471,plain,
    ( ~ spl9_117
    | spl9_678
    | ~ spl9_658 ),
    inference(avatar_split_clause,[],[f17428,f17383,f17469,f1072])).

fof(f1072,plain,
    ( spl9_117
  <=> ~ v1_funct_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_117])])).

fof(f17469,plain,
    ( spl9_678
  <=> ! [X32,X34,X33] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X32,u1_struct_0(sK1)))
        | v1_xboole_0(k5_relat_1(X33,k5_relat_1(sK3,sK4)))
        | ~ r1_tarski(X33,k2_zfmisc_1(X32,X34))
        | ~ v1_funct_1(X33) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_678])])).

fof(f17428,plain,
    ( ! [X33,X34,X32] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X32,u1_struct_0(sK1)))
        | v1_xboole_0(k5_relat_1(X33,k5_relat_1(sK3,sK4)))
        | ~ v1_funct_1(k5_relat_1(sK3,sK4))
        | ~ v1_funct_1(X33)
        | ~ r1_tarski(X33,k2_zfmisc_1(X32,X34)) )
    | ~ spl9_658 ),
    inference(resolution,[],[f17384,f10696])).

fof(f10696,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X4,X2))
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X2))
      | v1_xboole_0(k5_relat_1(X0,X3))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X5)) ) ),
    inference(resolution,[],[f10493,f106])).

fof(f10493,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X3))
      | v1_xboole_0(k5_relat_1(X0,X4))
      | ~ v1_funct_1(X4)
      | ~ r1_tarski(X4,k2_zfmisc_1(X5,X3)) ) ),
    inference(resolution,[],[f10492,f106])).

fof(f10492,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_xboole_0(k2_zfmisc_1(X0,X3))
      | v1_xboole_0(k5_relat_1(X4,X5))
      | ~ v1_funct_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f10491])).

fof(f10491,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_xboole_0(k2_zfmisc_1(X0,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f3437,f116])).

fof(f3437,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(k1_partfun1(X2,X3,X5,X4,X1,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X1)
      | ~ v1_xboole_0(k2_zfmisc_1(X2,X4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f829,f280])).

fof(f829,plain,(
    ! [X78,X76,X74,X72,X77,X75,X73] :
      ( ~ r2_hidden(X78,k1_partfun1(X76,X77,X73,X74,X75,X72))
      | ~ v1_funct_1(X72)
      | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))
      | ~ v1_funct_1(X75)
      | ~ v1_xboole_0(k2_zfmisc_1(X76,X74))
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) ) ),
    inference(resolution,[],[f118,f111])).

fof(f17467,plain,
    ( spl9_676
    | ~ spl9_117
    | ~ spl9_658 ),
    inference(avatar_split_clause,[],[f17425,f17383,f1072,f17465])).

fof(f17465,plain,
    ( spl9_676
  <=> ! [X29,X31,X28,X30] :
        ( m1_subset_1(X28,k2_zfmisc_1(u1_struct_0(sK0),X29))
        | ~ r1_tarski(X30,k2_zfmisc_1(X31,X29))
        | ~ v1_funct_1(X30)
        | ~ r2_hidden(X28,k5_relat_1(k5_relat_1(sK3,sK4),X30)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_676])])).

fof(f17425,plain,
    ( ! [X30,X28,X31,X29] :
        ( ~ v1_funct_1(k5_relat_1(sK3,sK4))
        | m1_subset_1(X28,k2_zfmisc_1(u1_struct_0(sK0),X29))
        | ~ r2_hidden(X28,k5_relat_1(k5_relat_1(sK3,sK4),X30))
        | ~ v1_funct_1(X30)
        | ~ r1_tarski(X30,k2_zfmisc_1(X31,X29)) )
    | ~ spl9_658 ),
    inference(resolution,[],[f17384,f9187])).

fof(f9187,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X3,X5))
      | ~ v1_funct_1(X1)
      | m1_subset_1(X2,k2_zfmisc_1(X3,X4))
      | ~ r2_hidden(X2,k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X6,X4)) ) ),
    inference(resolution,[],[f8565,f106])).

fof(f8565,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(X3)
      | m1_subset_1(X4,k2_zfmisc_1(X5,X2))
      | ~ r2_hidden(X4,k5_relat_1(X3,X0))
      | ~ r1_tarski(X3,k2_zfmisc_1(X5,X6)) ) ),
    inference(resolution,[],[f2798,f106])).

fof(f2798,plain,(
    ! [X294,X300,X296,X298,X295,X297,X299] :
      ( ~ m1_subset_1(X297,k1_zfmisc_1(k2_zfmisc_1(X298,X299)))
      | ~ v1_funct_1(X294)
      | ~ m1_subset_1(X294,k1_zfmisc_1(k2_zfmisc_1(X295,X296)))
      | ~ v1_funct_1(X297)
      | m1_subset_1(X300,k2_zfmisc_1(X298,X296))
      | ~ r2_hidden(X300,k5_relat_1(X297,X294)) ) ),
    inference(resolution,[],[f833,f110])).

fof(f17463,plain,
    ( spl9_674
    | ~ spl9_117
    | ~ spl9_658 ),
    inference(avatar_split_clause,[],[f17422,f17383,f1072,f17461])).

fof(f17461,plain,
    ( spl9_674
  <=> ! [X22,X25,X23,X24] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X22))
        | ~ r2_hidden(X23,k5_relat_1(k5_relat_1(sK3,sK4),X24))
        | ~ r1_tarski(X24,k2_zfmisc_1(X25,X22))
        | ~ v1_funct_1(X24) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_674])])).

fof(f17422,plain,
    ( ! [X24,X23,X25,X22] :
        ( ~ v1_funct_1(k5_relat_1(sK3,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X22))
        | ~ r2_hidden(X23,k5_relat_1(k5_relat_1(sK3,sK4),X24))
        | ~ v1_funct_1(X24)
        | ~ r1_tarski(X24,k2_zfmisc_1(X25,X22)) )
    | ~ spl9_658 ),
    inference(resolution,[],[f17384,f6017])).

fof(f6017,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X5))
      | ~ v1_funct_1(X1)
      | ~ v1_xboole_0(k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X4,k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X6,X3)) ) ),
    inference(resolution,[],[f5399,f106])).

fof(f5399,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(X3)
      | ~ v1_xboole_0(k2_zfmisc_1(X4,X2))
      | ~ r2_hidden(X5,k5_relat_1(X3,X0))
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X6)) ) ),
    inference(resolution,[],[f2799,f106])).

fof(f2799,plain,(
    ! [X302,X304,X306,X301,X303,X305,X307] :
      ( ~ m1_subset_1(X304,k1_zfmisc_1(k2_zfmisc_1(X305,X306)))
      | ~ v1_funct_1(X301)
      | ~ m1_subset_1(X301,k1_zfmisc_1(k2_zfmisc_1(X302,X303)))
      | ~ v1_funct_1(X304)
      | ~ v1_xboole_0(k2_zfmisc_1(X305,X303))
      | ~ r2_hidden(X307,k5_relat_1(X304,X301)) ) ),
    inference(resolution,[],[f833,f111])).

fof(f17459,plain,
    ( spl9_672
    | ~ spl9_117
    | ~ spl9_658 ),
    inference(avatar_split_clause,[],[f17417,f17383,f1072,f17457])).

fof(f17457,plain,
    ( spl9_672
  <=> ! [X18,X17,X19] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),X17))
        | ~ v1_funct_1(X17)
        | ~ r1_tarski(X17,k2_zfmisc_1(X18,X19)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_672])])).

fof(f17417,plain,
    ( ! [X19,X17,X18] :
        ( ~ v1_funct_1(k5_relat_1(sK3,sK4))
        | v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),X17))
        | ~ r1_tarski(X17,k2_zfmisc_1(X18,X19))
        | ~ v1_funct_1(X17) )
    | ~ spl9_658 ),
    inference(resolution,[],[f17384,f2909])).

fof(f2909,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X4,X5))
      | ~ v1_funct_1(X1)
      | v1_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,X3))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f2673,f106])).

fof(f2673,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(X1)
      | v1_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(X0,k2_zfmisc_1(X4,X5)) ) ),
    inference(resolution,[],[f2672,f106])).

fof(f2672,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | v1_relat_1(k5_relat_1(X4,X5)) ) ),
    inference(duplicate_literal_removal,[],[f2671])).

fof(f2671,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_relat_1(k5_relat_1(X4,X5))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f819,f116])).

fof(f819,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f118,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',cc1_relset_1)).

fof(f17455,plain,
    ( ~ spl9_117
    | spl9_670
    | ~ spl9_658 ),
    inference(avatar_split_clause,[],[f17412,f17383,f17453,f1072])).

fof(f17453,plain,
    ( spl9_670
  <=> ! [X16,X15,X14] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(sK3,sK4),X14))
        | ~ v1_funct_1(X14)
        | ~ r1_tarski(X14,k2_zfmisc_1(X15,X16)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_670])])).

fof(f17412,plain,
    ( ! [X14,X15,X16] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(sK3,sK4),X14))
        | ~ v1_funct_1(k5_relat_1(sK3,sK4))
        | ~ r1_tarski(X14,k2_zfmisc_1(X15,X16))
        | ~ v1_funct_1(X14) )
    | ~ spl9_658 ),
    inference(resolution,[],[f17384,f1145])).

fof(f1145,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X4,X5))
      | v1_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,X3))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f985,f106])).

fof(f985,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) ) ),
    inference(resolution,[],[f682,f106])).

fof(f682,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k5_relat_1(X4,X5))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f681])).

fof(f681,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f117,f116])).

fof(f117,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f17451,plain,
    ( spl9_668
    | ~ spl9_79
    | ~ spl9_658 ),
    inference(avatar_split_clause,[],[f17408,f17383,f484,f17449])).

fof(f17449,plain,
    ( spl9_668
  <=> ! [X11,X12] : ~ r2_hidden(X11,k10_relat_1(k5_relat_1(sK3,sK4),X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_668])])).

fof(f17408,plain,
    ( ! [X12,X11] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ r2_hidden(X11,k10_relat_1(k5_relat_1(sK3,sK4),X12)) )
    | ~ spl9_658 ),
    inference(resolution,[],[f17384,f585])).

fof(f585,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r1_tarski(X5,k2_zfmisc_1(X6,X7))
      | ~ v1_xboole_0(X6)
      | ~ r2_hidden(X8,k10_relat_1(X5,X9)) ) ),
    inference(resolution,[],[f543,f111])).

fof(f17447,plain,
    ( spl9_666
    | spl9_100
    | ~ spl9_25
    | ~ spl9_23
    | ~ spl9_117
    | ~ spl9_131
    | ~ spl9_658 ),
    inference(avatar_split_clause,[],[f17403,f17383,f2033,f1072,f199,f206,f684,f17445])).

fof(f17445,plain,
    ( spl9_666
  <=> r1_tarski(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_666])])).

fof(f684,plain,
    ( spl9_100
  <=> v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f206,plain,
    ( spl9_25
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f199,plain,
    ( spl9_23
  <=> ~ l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f2033,plain,
    ( spl9_131
  <=> ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).

fof(f17403,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | r1_tarski(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),u1_struct_0(sK1))
    | ~ spl9_658 ),
    inference(resolution,[],[f17384,f4357])).

fof(f4357,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(X8,k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)))
      | ~ v1_funct_2(X8,u1_struct_0(X9),u1_struct_0(X10))
      | ~ v1_funct_1(X8)
      | ~ l1_pre_topc(X10)
      | ~ l1_pre_topc(X9)
      | v5_pre_topc(X8,X9,X10)
      | r1_tarski(sK5(X9,X10,X8),u1_struct_0(X10)) ) ),
    inference(resolution,[],[f1586,f105])).

fof(f1586,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X2,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))) ) ),
    inference(resolution,[],[f95,f106])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
                    & v4_pre_topc(sK5(X0,X1,X2),X1)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f69,f70])).

fof(f70,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
        & v4_pre_topc(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',d12_pre_topc)).

fof(f17440,plain,
    ( spl9_664
    | ~ spl9_289
    | spl9_100
    | ~ spl9_25
    | ~ spl9_23
    | ~ spl9_117
    | ~ spl9_131
    | ~ spl9_658 ),
    inference(avatar_split_clause,[],[f17402,f17383,f2033,f1072,f199,f206,f684,f4680,f17438])).

fof(f17438,plain,
    ( spl9_664
  <=> ! [X7] : ~ r2_hidden(X7,sK5(sK0,sK1,k5_relat_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_664])])).

fof(f4680,plain,
    ( spl9_289
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_289])])).

fof(f17402,plain,
    ( ! [X7] :
        ( ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k5_relat_1(sK3,sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
        | ~ v1_xboole_0(u1_struct_0(sK1))
        | ~ r2_hidden(X7,sK5(sK0,sK1,k5_relat_1(sK3,sK4))) )
    | ~ spl9_658 ),
    inference(resolution,[],[f17384,f4356])).

fof(f4356,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6)))
      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X6))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X6)
      | ~ l1_pre_topc(X5)
      | v5_pre_topc(X4,X5,X6)
      | ~ v1_xboole_0(u1_struct_0(X6))
      | ~ r2_hidden(X7,sK5(X5,X6,X4)) ) ),
    inference(resolution,[],[f1586,f111])).

fof(f17436,plain,
    ( spl9_662
    | spl9_100
    | ~ spl9_25
    | ~ spl9_23
    | ~ spl9_117
    | ~ spl9_131
    | ~ spl9_658 ),
    inference(avatar_split_clause,[],[f17401,f17383,f2033,f1072,f199,f206,f684,f17434])).

fof(f17434,plain,
    ( spl9_662
  <=> ! [X6] :
        ( m1_subset_1(X6,u1_struct_0(sK1))
        | ~ r2_hidden(X6,sK5(sK0,sK1,k5_relat_1(sK3,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_662])])).

fof(f17401,plain,
    ( ! [X6] :
        ( ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k5_relat_1(sK3,sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0)
        | v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
        | m1_subset_1(X6,u1_struct_0(sK1))
        | ~ r2_hidden(X6,sK5(sK0,sK1,k5_relat_1(sK3,sK4))) )
    | ~ spl9_658 ),
    inference(resolution,[],[f17384,f4355])).

fof(f4355,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(X0,X1,X2)
      | m1_subset_1(X3,u1_struct_0(X2))
      | ~ r2_hidden(X3,sK5(X1,X2,X0)) ) ),
    inference(resolution,[],[f1586,f110])).

fof(f17396,plain,
    ( spl9_578
    | ~ spl9_17
    | spl9_582
    | ~ spl9_11
    | spl9_659 ),
    inference(avatar_split_clause,[],[f17395,f17386,f157,f15333,f178,f15324])).

fof(f17395,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) )
    | ~ spl9_659 ),
    inference(resolution,[],[f17387,f2800])).

fof(f2800,plain,(
    ! [X313,X308,X310,X312,X309,X311] :
      ( r1_tarski(k5_relat_1(X311,X308),k2_zfmisc_1(X312,X310))
      | ~ v1_funct_1(X308)
      | ~ m1_subset_1(X311,k1_zfmisc_1(k2_zfmisc_1(X312,X313)))
      | ~ v1_funct_1(X311)
      | ~ m1_subset_1(X308,k1_zfmisc_1(k2_zfmisc_1(X309,X310))) ) ),
    inference(resolution,[],[f833,f105])).

fof(f17387,plain,
    ( ~ r1_tarski(k5_relat_1(sK3,sK4),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl9_659 ),
    inference(avatar_component_clause,[],[f17386])).

fof(f17394,plain,
    ( ~ spl9_581
    | ~ spl9_117
    | ~ spl9_25
    | ~ spl9_659
    | ~ spl9_661
    | ~ spl9_131
    | ~ spl9_23
    | spl9_100
    | ~ spl9_350
    | ~ spl9_618 ),
    inference(avatar_split_clause,[],[f17381,f15557,f5812,f684,f199,f2033,f17392,f17386,f206,f1072,f15327])).

fof(f15327,plain,
    ( spl9_581
  <=> ~ v4_pre_topc(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_581])])).

fof(f5812,plain,
    ( spl9_350
  <=> ! [X77,X76] :
        ( v4_pre_topc(k10_relat_1(sK4,sK5(X76,sK1,X77)),sK2)
        | ~ r1_tarski(X77,k2_zfmisc_1(u1_struct_0(X76),u1_struct_0(sK1)))
        | ~ l1_pre_topc(X76)
        | ~ v1_funct_1(X77)
        | ~ v1_funct_2(X77,u1_struct_0(X76),u1_struct_0(sK1))
        | v5_pre_topc(X77,X76,sK1)
        | ~ v4_pre_topc(sK5(X76,sK1,X77),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_350])])).

fof(f15557,plain,
    ( spl9_618
  <=> ! [X42] :
        ( v5_pre_topc(k5_relat_1(sK3,sK4),sK0,X42)
        | ~ v4_pre_topc(k10_relat_1(sK4,sK5(sK0,X42,k5_relat_1(sK3,sK4))),sK2)
        | ~ l1_pre_topc(X42)
        | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(X42))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X42)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_618])])).

fof(f17381,plain,
    ( v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r1_tarski(k5_relat_1(sK3,sK4),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ v4_pre_topc(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),sK1)
    | ~ spl9_350
    | ~ spl9_618 ),
    inference(duplicate_literal_removal,[],[f17379])).

fof(f17379,plain,
    ( v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r1_tarski(k5_relat_1(sK3,sK4),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | ~ v4_pre_topc(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),sK1)
    | ~ spl9_350
    | ~ spl9_618 ),
    inference(resolution,[],[f15558,f5813])).

fof(f5813,plain,
    ( ! [X76,X77] :
        ( v4_pre_topc(k10_relat_1(sK4,sK5(X76,sK1,X77)),sK2)
        | ~ r1_tarski(X77,k2_zfmisc_1(u1_struct_0(X76),u1_struct_0(sK1)))
        | ~ l1_pre_topc(X76)
        | ~ v1_funct_1(X77)
        | ~ v1_funct_2(X77,u1_struct_0(X76),u1_struct_0(sK1))
        | v5_pre_topc(X77,X76,sK1)
        | ~ v4_pre_topc(sK5(X76,sK1,X77),sK1) )
    | ~ spl9_350 ),
    inference(avatar_component_clause,[],[f5812])).

fof(f15558,plain,
    ( ! [X42] :
        ( ~ v4_pre_topc(k10_relat_1(sK4,sK5(sK0,X42,k5_relat_1(sK3,sK4))),sK2)
        | v5_pre_topc(k5_relat_1(sK3,sK4),sK0,X42)
        | ~ l1_pre_topc(X42)
        | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(X42))
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X42)))) )
    | ~ spl9_618 ),
    inference(avatar_component_clause,[],[f15557])).

fof(f17270,plain,
    ( ~ spl9_23
    | spl9_578
    | ~ spl9_11
    | spl9_656
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f17266,f1978,f17268,f157,f15324,f199])).

fof(f17268,plain,
    ( spl9_656
  <=> ! [X1,X3,X5,X0,X2,X4,X6] :
        ( ~ v1_funct_2(k10_relat_1(k10_relat_1(X0,X1),X2),u1_struct_0(X3),u1_struct_0(sK2))
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_1(k5_relat_1(k10_relat_1(k10_relat_1(X0,X1),X2),sK4))
        | v5_pre_topc(k5_relat_1(k10_relat_1(k10_relat_1(X0,X1),X2),sK4),X3,sK1)
        | v4_pre_topc(sK5(X3,sK1,k5_relat_1(k10_relat_1(k10_relat_1(X0,X1),X2),sK4)),sK1)
        | ~ m1_subset_1(k10_relat_1(k10_relat_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),X6)))
        | ~ r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)),X4),X5))
        | ~ v1_funct_1(k10_relat_1(k10_relat_1(X0,X1),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_656])])).

fof(f1978,plain,
    ( spl9_126
  <=> ! [X106,X105] :
        ( v1_funct_2(k5_relat_1(X105,sK4),X106,u1_struct_0(sK1))
        | ~ v1_funct_1(X105)
        | ~ v1_funct_2(X105,X106,u1_struct_0(sK2))
        | ~ m1_subset_1(X105,k1_zfmisc_1(k2_zfmisc_1(X106,u1_struct_0(sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_126])])).

fof(f17266,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] :
        ( ~ v1_funct_2(k10_relat_1(k10_relat_1(X0,X1),X2),u1_struct_0(X3),u1_struct_0(sK2))
        | ~ v1_funct_1(k10_relat_1(k10_relat_1(X0,X1),X2))
        | ~ r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)),X4),X5))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(k10_relat_1(k10_relat_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),X6)))
        | v4_pre_topc(sK5(X3,sK1,k5_relat_1(k10_relat_1(k10_relat_1(X0,X1),X2),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(k10_relat_1(k10_relat_1(X0,X1),X2),sK4),X3,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X7,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(k10_relat_1(k10_relat_1(X0,X1),X2),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X3) )
    | ~ spl9_126 ),
    inference(duplicate_literal_removal,[],[f17264])).

fof(f17264,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] :
        ( ~ v1_funct_2(k10_relat_1(k10_relat_1(X0,X1),X2),u1_struct_0(X3),u1_struct_0(sK2))
        | ~ v1_funct_1(k10_relat_1(k10_relat_1(X0,X1),X2))
        | ~ r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)),X4),X5))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(k10_relat_1(k10_relat_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),X6)))
        | ~ v1_funct_1(k10_relat_1(k10_relat_1(X0,X1),X2))
        | v4_pre_topc(sK5(X3,sK1,k5_relat_1(k10_relat_1(k10_relat_1(X0,X1),X2),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(k10_relat_1(k10_relat_1(X0,X1),X2),sK4),X3,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X7,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(k10_relat_1(k10_relat_1(X0,X1),X2),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X3) )
    | ~ spl9_126 ),
    inference(resolution,[],[f2020,f2781])).

fof(f2781,plain,(
    ! [X154,X152,X151,X155,X153,X150] :
      ( ~ v1_funct_2(k5_relat_1(X153,X150),u1_struct_0(X154),u1_struct_0(X152))
      | ~ v1_funct_1(X150)
      | ~ m1_subset_1(X153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X154),X155)))
      | ~ v1_funct_1(X153)
      | v4_pre_topc(sK5(X154,X152,k5_relat_1(X153,X150)),X152)
      | v5_pre_topc(k5_relat_1(X153,X150),X154,X152)
      | ~ m1_subset_1(X150,k1_zfmisc_1(k2_zfmisc_1(X151,u1_struct_0(X152))))
      | ~ v1_funct_1(k5_relat_1(X153,X150))
      | ~ l1_pre_topc(X152)
      | ~ l1_pre_topc(X154) ) ),
    inference(resolution,[],[f833,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v4_pre_topc(sK5(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f2020,plain,
    ( ! [X39,X43,X41,X44,X42,X40] :
        ( v1_funct_2(k5_relat_1(k10_relat_1(k10_relat_1(X39,X40),X41),sK4),X42,u1_struct_0(sK1))
        | ~ v1_funct_2(k10_relat_1(k10_relat_1(X39,X40),X41),X42,u1_struct_0(sK2))
        | ~ v1_funct_1(k10_relat_1(k10_relat_1(X39,X40),X41))
        | ~ r1_tarski(X39,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X42,u1_struct_0(sK2)),X43),X44)) )
    | ~ spl9_126 ),
    inference(resolution,[],[f1979,f587])).

fof(f587,plain,(
    ! [X14,X19,X17,X15,X18,X16] :
      ( m1_subset_1(k10_relat_1(k10_relat_1(X14,X18),X19),k1_zfmisc_1(X15))
      | ~ r1_tarski(X14,k2_zfmisc_1(k2_zfmisc_1(X15,X16),X17)) ) ),
    inference(resolution,[],[f543,f470])).

fof(f1979,plain,
    ( ! [X105,X106] :
        ( ~ m1_subset_1(X105,k1_zfmisc_1(k2_zfmisc_1(X106,u1_struct_0(sK2))))
        | ~ v1_funct_1(X105)
        | ~ v1_funct_2(X105,X106,u1_struct_0(sK2))
        | v1_funct_2(k5_relat_1(X105,sK4),X106,u1_struct_0(sK1)) )
    | ~ spl9_126 ),
    inference(avatar_component_clause,[],[f1978])).

fof(f17104,plain,
    ( ~ spl9_23
    | spl9_654
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f17092,f5674,f17102,f199])).

fof(f17102,plain,
    ( spl9_654
  <=> ! [X9,X5,X7,X8,X6] :
        ( ~ v1_funct_1(X5)
        | ~ v4_pre_topc(sK5(X7,sK1,k5_relat_1(X6,X5)),sK1)
        | v4_pre_topc(k10_relat_1(sK4,sK5(X7,sK1,k5_relat_1(X6,X5))),sK2)
        | ~ l1_pre_topc(X7)
        | ~ v1_funct_1(k5_relat_1(X6,X5))
        | ~ v1_funct_2(k5_relat_1(X6,X5),u1_struct_0(X7),u1_struct_0(sK1))
        | v5_pre_topc(k5_relat_1(X6,X5),X7,sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X9,u1_struct_0(sK1))))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),X8)))
        | ~ v1_funct_1(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_654])])).

fof(f5674,plain,
    ( spl9_320
  <=> ! [X139] :
        ( ~ v4_pre_topc(X139,sK1)
        | v4_pre_topc(k10_relat_1(sK4,X139),sK2)
        | ~ m1_subset_1(X139,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_320])])).

fof(f17092,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ v1_funct_1(X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),X8)))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X9,u1_struct_0(sK1))))
        | v5_pre_topc(k5_relat_1(X6,X5),X7,sK1)
        | ~ v1_funct_2(k5_relat_1(X6,X5),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v1_funct_1(k5_relat_1(X6,X5))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X7)
        | v4_pre_topc(k10_relat_1(sK4,sK5(X7,sK1,k5_relat_1(X6,X5))),sK2)
        | ~ v4_pre_topc(sK5(X7,sK1,k5_relat_1(X6,X5)),sK1) )
    | ~ spl9_320 ),
    inference(resolution,[],[f2780,f5675])).

fof(f5675,plain,
    ( ! [X139] :
        ( ~ m1_subset_1(X139,k1_zfmisc_1(u1_struct_0(sK1)))
        | v4_pre_topc(k10_relat_1(sK4,X139),sK2)
        | ~ v4_pre_topc(X139,sK1) )
    | ~ spl9_320 ),
    inference(avatar_component_clause,[],[f5674])).

fof(f2780,plain,(
    ! [X146,X144,X149,X147,X145,X148] :
      ( m1_subset_1(sK5(X148,X146,k5_relat_1(X147,X144)),k1_zfmisc_1(u1_struct_0(X146)))
      | ~ v1_funct_1(X144)
      | ~ m1_subset_1(X147,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X148),X149)))
      | ~ v1_funct_1(X147)
      | ~ m1_subset_1(X144,k1_zfmisc_1(k2_zfmisc_1(X145,u1_struct_0(X146))))
      | v5_pre_topc(k5_relat_1(X147,X144),X148,X146)
      | ~ v1_funct_2(k5_relat_1(X147,X144),u1_struct_0(X148),u1_struct_0(X146))
      | ~ v1_funct_1(k5_relat_1(X147,X144))
      | ~ l1_pre_topc(X146)
      | ~ l1_pre_topc(X148) ) ),
    inference(resolution,[],[f833,f95])).

fof(f17100,plain,
    ( ~ spl9_19
    | spl9_652
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f17091,f5670,f17098,f185])).

fof(f185,plain,
    ( spl9_19
  <=> ~ l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f17098,plain,
    ( spl9_652
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v1_funct_1(X0)
        | ~ v4_pre_topc(sK5(X2,sK2,k5_relat_1(X1,X0)),sK2)
        | v4_pre_topc(k10_relat_1(sK3,sK5(X2,sK2,k5_relat_1(X1,X0))),sK0)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(k5_relat_1(X1,X0))
        | ~ v1_funct_2(k5_relat_1(X1,X0),u1_struct_0(X2),u1_struct_0(sK2))
        | v5_pre_topc(k5_relat_1(X1,X0),X2,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(sK2))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X3)))
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_652])])).

fof(f5670,plain,
    ( spl9_318
  <=> ! [X138] :
        ( ~ v4_pre_topc(X138,sK2)
        | v4_pre_topc(k10_relat_1(sK3,X138),sK0)
        | ~ m1_subset_1(X138,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_318])])).

fof(f17091,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X3)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(sK2))))
        | v5_pre_topc(k5_relat_1(X1,X0),X2,sK2)
        | ~ v1_funct_2(k5_relat_1(X1,X0),u1_struct_0(X2),u1_struct_0(sK2))
        | ~ v1_funct_1(k5_relat_1(X1,X0))
        | ~ l1_pre_topc(sK2)
        | ~ l1_pre_topc(X2)
        | v4_pre_topc(k10_relat_1(sK3,sK5(X2,sK2,k5_relat_1(X1,X0))),sK0)
        | ~ v4_pre_topc(sK5(X2,sK2,k5_relat_1(X1,X0)),sK2) )
    | ~ spl9_318 ),
    inference(resolution,[],[f2780,f5671])).

fof(f5671,plain,
    ( ! [X138] :
        ( ~ m1_subset_1(X138,k1_zfmisc_1(u1_struct_0(sK2)))
        | v4_pre_topc(k10_relat_1(sK3,X138),sK0)
        | ~ v4_pre_topc(X138,sK2) )
    | ~ spl9_318 ),
    inference(avatar_component_clause,[],[f5670])).

fof(f15623,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_650
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15521,f5674,f15621,f185,f333])).

fof(f15621,plain,
    ( spl9_650
  <=> ! [X106,X105] :
        ( v5_pre_topc(k5_relat_1(sK4,X105),sK2,X106)
        | ~ r1_tarski(k10_relat_1(X105,sK5(sK2,X106,k5_relat_1(sK4,X105))),u1_struct_0(sK1))
        | ~ v4_pre_topc(k10_relat_1(X105,sK5(sK2,X106,k5_relat_1(sK4,X105))),sK1)
        | ~ v1_relat_1(X105)
        | ~ l1_pre_topc(X106)
        | ~ v1_funct_1(k5_relat_1(sK4,X105))
        | ~ v1_funct_2(k5_relat_1(sK4,X105),u1_struct_0(sK2),u1_struct_0(X106))
        | ~ m1_subset_1(k5_relat_1(sK4,X105),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X106)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_650])])).

fof(f15521,plain,
    ( ! [X105,X106] :
        ( v5_pre_topc(k5_relat_1(sK4,X105),sK2,X106)
        | ~ m1_subset_1(k5_relat_1(sK4,X105),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X106))))
        | ~ v1_funct_2(k5_relat_1(sK4,X105),u1_struct_0(sK2),u1_struct_0(X106))
        | ~ v1_funct_1(k5_relat_1(sK4,X105))
        | ~ l1_pre_topc(X106)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(X105)
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(X105,sK5(sK2,X106,k5_relat_1(sK4,X105))),sK1)
        | ~ r1_tarski(k10_relat_1(X105,sK5(sK2,X106,k5_relat_1(sK4,X105))),u1_struct_0(sK1)) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5787])).

fof(f5787,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK4,X0),sK2)
        | ~ v4_pre_topc(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK1)) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f106])).

fof(f5102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_pre_topc(k10_relat_1(X0,k10_relat_1(X1,sK5(X2,X3,k5_relat_1(X0,X1)))),X2)
      | v5_pre_topc(k5_relat_1(X0,X1),X2,X3)
      | ~ m1_subset_1(k5_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ v1_funct_2(k5_relat_1(X0,X1),u1_struct_0(X2),u1_struct_0(X3))
      | ~ v1_funct_1(k5_relat_1(X0,X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f2198,f100])).

fof(f2198,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k10_relat_1(X2,sK5(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f2197])).

fof(f2197,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k10_relat_1(X2,sK5(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ),
    inference(superposition,[],[f97,f113])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f15619,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_648
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15520,f5670,f15617,f206,f326])).

fof(f15617,plain,
    ( spl9_648
  <=> ! [X104,X103] :
        ( v5_pre_topc(k5_relat_1(sK3,X103),sK0,X104)
        | ~ r1_tarski(k10_relat_1(X103,sK5(sK0,X104,k5_relat_1(sK3,X103))),u1_struct_0(sK2))
        | ~ v4_pre_topc(k10_relat_1(X103,sK5(sK0,X104,k5_relat_1(sK3,X103))),sK2)
        | ~ v1_relat_1(X103)
        | ~ l1_pre_topc(X104)
        | ~ v1_funct_1(k5_relat_1(sK3,X103))
        | ~ v1_funct_2(k5_relat_1(sK3,X103),u1_struct_0(sK0),u1_struct_0(X104))
        | ~ m1_subset_1(k5_relat_1(sK3,X103),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X104)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_648])])).

fof(f15520,plain,
    ( ! [X103,X104] :
        ( v5_pre_topc(k5_relat_1(sK3,X103),sK0,X104)
        | ~ m1_subset_1(k5_relat_1(sK3,X103),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X104))))
        | ~ v1_funct_2(k5_relat_1(sK3,X103),u1_struct_0(sK0),u1_struct_0(X104))
        | ~ v1_funct_1(k5_relat_1(sK3,X103))
        | ~ l1_pre_topc(X104)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(X103)
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(X103,sK5(sK0,X104,k5_relat_1(sK3,X103))),sK2)
        | ~ r1_tarski(k10_relat_1(X103,sK5(sK0,X104,k5_relat_1(sK3,X103))),u1_struct_0(sK2)) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5677])).

fof(f5677,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK3,X0),sK0)
        | ~ v4_pre_topc(X0,sK2)
        | ~ r1_tarski(X0,u1_struct_0(sK2)) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f106])).

fof(f15615,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_646
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15519,f5674,f15613,f185,f333])).

fof(f15613,plain,
    ( spl9_646
  <=> ! [X98,X100,X102,X99,X101] :
        ( v5_pre_topc(k5_relat_1(sK4,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101)),sK2,X102)
        | ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99)))
        | ~ v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101),sK5(sK2,X102,k5_relat_1(sK4,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101)))),sK1)
        | ~ v1_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101))
        | ~ l1_pre_topc(X102)
        | ~ v1_funct_1(k5_relat_1(sK4,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101)))
        | ~ v1_funct_2(k5_relat_1(sK4,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101)),u1_struct_0(sK2),u1_struct_0(X102))
        | ~ m1_subset_1(k5_relat_1(sK4,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X102)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_646])])).

fof(f15519,plain,
    ( ! [X101,X99,X102,X100,X98] :
        ( v5_pre_topc(k5_relat_1(sK4,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101)),sK2,X102)
        | ~ m1_subset_1(k5_relat_1(sK4,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X102))))
        | ~ v1_funct_2(k5_relat_1(sK4,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101)),u1_struct_0(sK2),u1_struct_0(X102))
        | ~ v1_funct_1(k5_relat_1(sK4,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101)))
        | ~ l1_pre_topc(X102)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101))
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101),sK5(sK2,X102,k5_relat_1(sK4,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99,X100,X101)))),sK1)
        | ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X98),X99))) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5794])).

fof(f5794,plain,
    ( ! [X30,X28,X26,X29,X27] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X26),X27,X28,X29),X30)),sK2)
        | ~ v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK1),X26),X27,X28,X29),X30),sK1)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X26),X27))) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f544])).

fof(f544,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( m1_subset_1(k10_relat_1(k8_relset_1(k2_zfmisc_1(X4,X5),X6,X7,X8),X9),k1_zfmisc_1(X4))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))) ) ),
    inference(resolution,[],[f470,f112])).

fof(f15611,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_644
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15518,f5674,f15609,f185,f333])).

fof(f15609,plain,
    ( spl9_644
  <=> ! [X96,X93,X95,X97,X92,X94] :
        ( v5_pre_topc(k5_relat_1(sK4,k10_relat_1(X92,k10_relat_1(X93,X94))),sK2,X95)
        | ~ v1_relat_1(X92)
        | ~ v1_relat_1(X93)
        | ~ r1_tarski(k5_relat_1(X92,X93),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X96),X97))
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X92,k10_relat_1(X93,X94)),sK5(sK2,X95,k5_relat_1(sK4,k10_relat_1(X92,k10_relat_1(X93,X94))))),sK1)
        | ~ v1_relat_1(k10_relat_1(X92,k10_relat_1(X93,X94)))
        | ~ l1_pre_topc(X95)
        | ~ v1_funct_1(k5_relat_1(sK4,k10_relat_1(X92,k10_relat_1(X93,X94))))
        | ~ v1_funct_2(k5_relat_1(sK4,k10_relat_1(X92,k10_relat_1(X93,X94))),u1_struct_0(sK2),u1_struct_0(X95))
        | ~ m1_subset_1(k5_relat_1(sK4,k10_relat_1(X92,k10_relat_1(X93,X94))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X95)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_644])])).

fof(f15518,plain,
    ( ! [X94,X92,X97,X95,X93,X96] :
        ( v5_pre_topc(k5_relat_1(sK4,k10_relat_1(X92,k10_relat_1(X93,X94))),sK2,X95)
        | ~ m1_subset_1(k5_relat_1(sK4,k10_relat_1(X92,k10_relat_1(X93,X94))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X95))))
        | ~ v1_funct_2(k5_relat_1(sK4,k10_relat_1(X92,k10_relat_1(X93,X94))),u1_struct_0(sK2),u1_struct_0(X95))
        | ~ v1_funct_1(k5_relat_1(sK4,k10_relat_1(X92,k10_relat_1(X93,X94))))
        | ~ l1_pre_topc(X95)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(k10_relat_1(X92,k10_relat_1(X93,X94)))
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X92,k10_relat_1(X93,X94)),sK5(sK2,X95,k5_relat_1(sK4,k10_relat_1(X92,k10_relat_1(X93,X94))))),sK1)
        | ~ r1_tarski(k5_relat_1(X92,X93),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X96),X97))
        | ~ v1_relat_1(X93)
        | ~ v1_relat_1(X92) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5801])).

fof(f5801,plain,
    ( ! [X61,X66,X64,X62,X65,X63] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(k10_relat_1(X61,k10_relat_1(X62,X63)),X64)),sK2)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X61,k10_relat_1(X62,X63)),X64),sK1)
        | ~ r1_tarski(k5_relat_1(X61,X62),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X65),X66))
        | ~ v1_relat_1(X62)
        | ~ v1_relat_1(X61) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f672])).

fof(f672,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_relat_1(k10_relat_1(X0,k10_relat_1(X1,X2)),X3),k1_zfmisc_1(X4))
      | ~ r1_tarski(k5_relat_1(X0,X1),k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f587,f100])).

fof(f15607,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_642
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15517,f5674,f15605,f185,f333])).

fof(f15605,plain,
    ( spl9_642
  <=> ! [X86,X89,X91,X87,X88,X90] :
        ( v5_pre_topc(k5_relat_1(sK4,k10_relat_1(X86,k10_relat_1(X87,X88))),sK2,X89)
        | ~ v1_relat_1(X86)
        | ~ v1_relat_1(X87)
        | ~ r1_tarski(k5_relat_1(X86,X87),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X90),X91))
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k5_relat_1(X86,X87),X88),sK5(sK2,X89,k5_relat_1(sK4,k10_relat_1(X86,k10_relat_1(X87,X88))))),sK1)
        | ~ v1_relat_1(k10_relat_1(X86,k10_relat_1(X87,X88)))
        | ~ l1_pre_topc(X89)
        | ~ v1_funct_1(k5_relat_1(sK4,k10_relat_1(X86,k10_relat_1(X87,X88))))
        | ~ v1_funct_2(k5_relat_1(sK4,k10_relat_1(X86,k10_relat_1(X87,X88))),u1_struct_0(sK2),u1_struct_0(X89))
        | ~ m1_subset_1(k5_relat_1(sK4,k10_relat_1(X86,k10_relat_1(X87,X88))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X89)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_642])])).

fof(f15517,plain,
    ( ! [X90,X88,X87,X91,X89,X86] :
        ( v5_pre_topc(k5_relat_1(sK4,k10_relat_1(X86,k10_relat_1(X87,X88))),sK2,X89)
        | ~ m1_subset_1(k5_relat_1(sK4,k10_relat_1(X86,k10_relat_1(X87,X88))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X89))))
        | ~ v1_funct_2(k5_relat_1(sK4,k10_relat_1(X86,k10_relat_1(X87,X88))),u1_struct_0(sK2),u1_struct_0(X89))
        | ~ v1_funct_1(k5_relat_1(sK4,k10_relat_1(X86,k10_relat_1(X87,X88))))
        | ~ l1_pre_topc(X89)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(k10_relat_1(X86,k10_relat_1(X87,X88)))
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k5_relat_1(X86,X87),X88),sK5(sK2,X89,k5_relat_1(sK4,k10_relat_1(X86,k10_relat_1(X87,X88))))),sK1)
        | ~ r1_tarski(k5_relat_1(X86,X87),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X90),X91))
        | ~ v1_relat_1(X87)
        | ~ v1_relat_1(X86) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5899])).

fof(f5899,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(k10_relat_1(X0,k10_relat_1(X1,X2)),X3)),sK2)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k5_relat_1(X0,X1),X2),X3),sK1)
        | ~ r1_tarski(k5_relat_1(X0,X1),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X4),X5))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl9_320 ),
    inference(superposition,[],[f5798,f100])).

fof(f5798,plain,
    ( ! [X47,X45,X48,X46,X44] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(k10_relat_1(X44,X45),X46)),sK2)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X44,X45),X46),sK1)
        | ~ r1_tarski(X44,k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X47),X48)) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f587])).

fof(f15603,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_640
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15516,f5674,f15601,f185,f333])).

fof(f15601,plain,
    ( spl9_640
  <=> ! [X82,X84,X79,X81,X83,X85,X80] :
        ( v5_pre_topc(k5_relat_1(sK4,k10_relat_1(k10_relat_1(X79,X80),X81)),sK2,X82)
        | ~ r1_tarski(X79,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X83),X84),X85))
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k10_relat_1(X79,X80),X81),sK5(sK2,X82,k5_relat_1(sK4,k10_relat_1(k10_relat_1(X79,X80),X81)))),sK1)
        | ~ v1_relat_1(k10_relat_1(k10_relat_1(X79,X80),X81))
        | ~ l1_pre_topc(X82)
        | ~ v1_funct_1(k5_relat_1(sK4,k10_relat_1(k10_relat_1(X79,X80),X81)))
        | ~ v1_funct_2(k5_relat_1(sK4,k10_relat_1(k10_relat_1(X79,X80),X81)),u1_struct_0(sK2),u1_struct_0(X82))
        | ~ m1_subset_1(k5_relat_1(sK4,k10_relat_1(k10_relat_1(X79,X80),X81)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X82)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_640])])).

fof(f15516,plain,
    ( ! [X80,X85,X83,X81,X79,X84,X82] :
        ( v5_pre_topc(k5_relat_1(sK4,k10_relat_1(k10_relat_1(X79,X80),X81)),sK2,X82)
        | ~ m1_subset_1(k5_relat_1(sK4,k10_relat_1(k10_relat_1(X79,X80),X81)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X82))))
        | ~ v1_funct_2(k5_relat_1(sK4,k10_relat_1(k10_relat_1(X79,X80),X81)),u1_struct_0(sK2),u1_struct_0(X82))
        | ~ v1_funct_1(k5_relat_1(sK4,k10_relat_1(k10_relat_1(X79,X80),X81)))
        | ~ l1_pre_topc(X82)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(k10_relat_1(k10_relat_1(X79,X80),X81))
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k10_relat_1(X79,X80),X81),sK5(sK2,X82,k5_relat_1(sK4,k10_relat_1(k10_relat_1(X79,X80),X81)))),sK1)
        | ~ r1_tarski(X79,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X83),X84),X85)) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5800])).

fof(f5800,plain,
    ( ! [X59,X57,X54,X60,X58,X56,X55] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(k10_relat_1(k10_relat_1(X54,X55),X56),X57)),sK2)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k10_relat_1(X54,X55),X56),X57),sK1)
        | ~ r1_tarski(X54,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X58),X59),X60)) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f668])).

fof(f668,plain,(
    ! [X39,X37,X43,X41,X38,X44,X42,X40] :
      ( m1_subset_1(k10_relat_1(k10_relat_1(k10_relat_1(X37,X42),X43),X44),k1_zfmisc_1(X38))
      | ~ r1_tarski(X37,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X38,X39),X40),X41)) ) ),
    inference(resolution,[],[f587,f470])).

fof(f15599,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_638
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15515,f5674,f15597,f185,f333])).

fof(f15597,plain,
    ( spl9_638
  <=> ! [X75,X77,X76,X78] :
        ( v5_pre_topc(k5_relat_1(sK4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77)),sK2,X78)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77),sK5(sK2,X78,k5_relat_1(sK4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77)))),sK1)
        | ~ v1_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77))
        | ~ l1_pre_topc(X78)
        | ~ v1_funct_1(k5_relat_1(sK4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77)))
        | ~ v1_funct_2(k5_relat_1(sK4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77)),u1_struct_0(sK2),u1_struct_0(X78))
        | ~ m1_subset_1(k5_relat_1(sK4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X78)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_638])])).

fof(f15515,plain,
    ( ! [X78,X76,X77,X75] :
        ( v5_pre_topc(k5_relat_1(sK4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77)),sK2,X78)
        | ~ m1_subset_1(k5_relat_1(sK4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X78))))
        | ~ v1_funct_2(k5_relat_1(sK4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77)),u1_struct_0(sK2),u1_struct_0(X78))
        | ~ v1_funct_1(k5_relat_1(sK4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77)))
        | ~ l1_pre_topc(X78)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77))
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77),sK5(sK2,X78,k5_relat_1(sK4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X75),X76))),X77)))),sK1) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5791])).

fof(f5791,plain,
    ( ! [X10,X8,X11,X9] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X8),X9))),X10),X11)),sK2)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X8),X9))),X10),X11),sK1) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f580])).

fof(f580,plain,(
    ! [X14,X12,X15,X13,X11] : m1_subset_1(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X12),X13))),X14),X15),k1_zfmisc_1(X11)) ),
    inference(resolution,[],[f547,f470])).

fof(f547,plain,(
    ! [X14,X12,X13] : m1_subset_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X12,X13))),X14),k1_zfmisc_1(X12)) ),
    inference(resolution,[],[f470,f99])).

fof(f15595,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_636
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15514,f5674,f15593,f185,f333])).

fof(f15593,plain,
    ( spl9_636
  <=> ! [X73,X69,X71,X72,X74,X70] :
        ( v5_pre_topc(k5_relat_1(sK4,k5_relat_1(X69,X70)),sK2,X71)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))
        | ~ v1_funct_1(X69)
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X72)))
        | ~ v1_funct_1(X70)
        | ~ v4_pre_topc(k10_relat_1(k5_relat_1(X69,X70),sK5(sK2,X71,k5_relat_1(sK4,k5_relat_1(X69,X70)))),sK1)
        | ~ v1_relat_1(k5_relat_1(X69,X70))
        | ~ l1_pre_topc(X71)
        | ~ v1_funct_1(k5_relat_1(sK4,k5_relat_1(X69,X70)))
        | ~ v1_funct_2(k5_relat_1(sK4,k5_relat_1(X69,X70)),u1_struct_0(sK2),u1_struct_0(X71))
        | ~ m1_subset_1(k5_relat_1(sK4,k5_relat_1(X69,X70)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X71)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_636])])).

fof(f15514,plain,
    ( ! [X70,X74,X72,X71,X69,X73] :
        ( v5_pre_topc(k5_relat_1(sK4,k5_relat_1(X69,X70)),sK2,X71)
        | ~ m1_subset_1(k5_relat_1(sK4,k5_relat_1(X69,X70)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X71))))
        | ~ v1_funct_2(k5_relat_1(sK4,k5_relat_1(X69,X70)),u1_struct_0(sK2),u1_struct_0(X71))
        | ~ v1_funct_1(k5_relat_1(sK4,k5_relat_1(X69,X70)))
        | ~ l1_pre_topc(X71)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(k5_relat_1(X69,X70))
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(k5_relat_1(X69,X70),sK5(sK2,X71,k5_relat_1(sK4,k5_relat_1(X69,X70)))),sK1)
        | ~ v1_funct_1(X70)
        | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X72)))
        | ~ v1_funct_1(X69)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5797])).

fof(f5797,plain,
    ( ! [X39,X43,X41,X38,X42,X40] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(k5_relat_1(X38,X39),X40)),sK2)
        | ~ v4_pre_topc(k10_relat_1(k5_relat_1(X38,X39),X40),sK1)
        | ~ v1_funct_1(X39)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X41)))
        | ~ v1_funct_1(X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f2763])).

fof(f2763,plain,(
    ! [X28,X26,X24,X23,X27,X25,X22] :
      ( m1_subset_1(k10_relat_1(k5_relat_1(X25,X22),X28),k1_zfmisc_1(X26))
      | ~ v1_funct_1(X22)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | ~ v1_funct_1(X25)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ),
    inference(resolution,[],[f833,f470])).

fof(f15591,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_634
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15513,f5674,f15589,f185,f333])).

fof(f15589,plain,
    ( spl9_634
  <=> ! [X65,X67,X64,X66,X68] :
        ( v5_pre_topc(k5_relat_1(sK4,sK6(k10_relat_1(X64,X65))),sK2,X66)
        | ~ r1_tarski(X64,k2_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X67)),X68))
        | v1_xboole_0(k10_relat_1(X64,X65))
        | ~ v4_pre_topc(k10_relat_1(sK6(k10_relat_1(X64,X65)),sK5(sK2,X66,k5_relat_1(sK4,sK6(k10_relat_1(X64,X65))))),sK1)
        | ~ v1_relat_1(sK6(k10_relat_1(X64,X65)))
        | ~ l1_pre_topc(X66)
        | ~ v1_funct_1(k5_relat_1(sK4,sK6(k10_relat_1(X64,X65))))
        | ~ v1_funct_2(k5_relat_1(sK4,sK6(k10_relat_1(X64,X65))),u1_struct_0(sK2),u1_struct_0(X66))
        | ~ m1_subset_1(k5_relat_1(sK4,sK6(k10_relat_1(X64,X65))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X66)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_634])])).

fof(f15513,plain,
    ( ! [X68,X66,X64,X67,X65] :
        ( v5_pre_topc(k5_relat_1(sK4,sK6(k10_relat_1(X64,X65))),sK2,X66)
        | ~ m1_subset_1(k5_relat_1(sK4,sK6(k10_relat_1(X64,X65))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X66))))
        | ~ v1_funct_2(k5_relat_1(sK4,sK6(k10_relat_1(X64,X65))),u1_struct_0(sK2),u1_struct_0(X66))
        | ~ v1_funct_1(k5_relat_1(sK4,sK6(k10_relat_1(X64,X65))))
        | ~ l1_pre_topc(X66)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(sK6(k10_relat_1(X64,X65)))
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(sK6(k10_relat_1(X64,X65)),sK5(sK2,X66,k5_relat_1(sK4,sK6(k10_relat_1(X64,X65))))),sK1)
        | v1_xboole_0(k10_relat_1(X64,X65))
        | ~ r1_tarski(X64,k2_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X67)),X68)) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5799])).

fof(f5799,plain,
    ( ! [X52,X50,X53,X51,X49] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(sK6(k10_relat_1(X49,X50)),X51)),sK2)
        | ~ v4_pre_topc(k10_relat_1(sK6(k10_relat_1(X49,X50)),X51),sK1)
        | v1_xboole_0(k10_relat_1(X49,X50))
        | ~ r1_tarski(X49,k2_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X52)),X53)) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f1728])).

fof(f1728,plain,(
    ! [X30,X28,X26,X31,X29,X27] :
      ( m1_subset_1(k10_relat_1(sK6(k10_relat_1(X26,X30)),X31),k1_zfmisc_1(X27))
      | v1_xboole_0(k10_relat_1(X26,X30))
      | ~ r1_tarski(X26,k2_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X27,X28)),X29)) ) ),
    inference(resolution,[],[f1722,f470])).

fof(f15587,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_632
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15512,f5674,f15585,f185,f333])).

fof(f15585,plain,
    ( spl9_632
  <=> ! [X63,X60,X62,X59,X61] :
        ( v5_pre_topc(k5_relat_1(sK4,k10_relat_1(X59,X60)),sK2,X61)
        | ~ r1_tarski(X59,k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X62),X63))
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X59,X60),sK5(sK2,X61,k5_relat_1(sK4,k10_relat_1(X59,X60)))),sK1)
        | ~ v1_relat_1(k10_relat_1(X59,X60))
        | ~ l1_pre_topc(X61)
        | ~ v1_funct_1(k5_relat_1(sK4,k10_relat_1(X59,X60)))
        | ~ v1_funct_2(k5_relat_1(sK4,k10_relat_1(X59,X60)),u1_struct_0(sK2),u1_struct_0(X61))
        | ~ m1_subset_1(k5_relat_1(sK4,k10_relat_1(X59,X60)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X61)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_632])])).

fof(f15512,plain,
    ( ! [X61,X59,X62,X60,X63] :
        ( v5_pre_topc(k5_relat_1(sK4,k10_relat_1(X59,X60)),sK2,X61)
        | ~ m1_subset_1(k5_relat_1(sK4,k10_relat_1(X59,X60)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X61))))
        | ~ v1_funct_2(k5_relat_1(sK4,k10_relat_1(X59,X60)),u1_struct_0(sK2),u1_struct_0(X61))
        | ~ v1_funct_1(k5_relat_1(sK4,k10_relat_1(X59,X60)))
        | ~ l1_pre_topc(X61)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(k10_relat_1(X59,X60))
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X59,X60),sK5(sK2,X61,k5_relat_1(sK4,k10_relat_1(X59,X60)))),sK1)
        | ~ r1_tarski(X59,k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X62),X63)) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5798])).

fof(f15583,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_630
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15511,f5674,f15581,f185,f333])).

fof(f15581,plain,
    ( spl9_630
  <=> ! [X58,X57] :
        ( v5_pre_topc(k5_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57)))))),sK2,X58)
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57)))))
        | ~ v4_pre_topc(k10_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57))))),sK5(sK2,X58,k5_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57)))))))),sK1)
        | ~ v1_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57))))))
        | ~ l1_pre_topc(X58)
        | ~ v1_funct_1(k5_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57)))))))
        | ~ v1_funct_2(k5_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57)))))),u1_struct_0(sK2),u1_struct_0(X58))
        | ~ m1_subset_1(k5_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57)))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X58)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_630])])).

fof(f15511,plain,
    ( ! [X57,X58] :
        ( v5_pre_topc(k5_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57)))))),sK2,X58)
        | ~ m1_subset_1(k5_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57)))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X58))))
        | ~ v1_funct_2(k5_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57)))))),u1_struct_0(sK2),u1_struct_0(X58))
        | ~ v1_funct_1(k5_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57)))))))
        | ~ l1_pre_topc(X58)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57))))))
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57))))),sK5(sK2,X58,k5_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57)))))))),sK1)
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X57))))) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5790])).

fof(f5790,plain,
    ( ! [X6,X7] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X6))))),X7)),sK2)
        | ~ v4_pre_topc(k10_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X6))))),X7),sK1)
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X6))))) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f548])).

fof(f548,plain,(
    ! [X17,X15,X16] :
      ( m1_subset_1(k10_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X15,X16))))),X17),k1_zfmisc_1(X15))
      | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X15,X16))))) ) ),
    inference(resolution,[],[f470,f374])).

fof(f15579,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_628
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15510,f5674,f15577,f185,f333])).

fof(f15577,plain,
    ( spl9_628
  <=> ! [X55,X56] :
        ( v5_pre_topc(k5_relat_1(sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55)))),sK2,X56)
        | ~ v4_pre_topc(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55))),sK5(sK2,X56,k5_relat_1(sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55)))))),sK1)
        | ~ v1_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55))))
        | ~ l1_pre_topc(X56)
        | ~ v1_funct_1(k5_relat_1(sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55)))))
        | ~ v1_funct_2(k5_relat_1(sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55)))),u1_struct_0(sK2),u1_struct_0(X56))
        | ~ m1_subset_1(k5_relat_1(sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X56)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_628])])).

fof(f15510,plain,
    ( ! [X56,X55] :
        ( v5_pre_topc(k5_relat_1(sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55)))),sK2,X56)
        | ~ m1_subset_1(k5_relat_1(sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X56))))
        | ~ v1_funct_2(k5_relat_1(sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55)))),u1_struct_0(sK2),u1_struct_0(X56))
        | ~ v1_funct_1(k5_relat_1(sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55)))))
        | ~ l1_pre_topc(X56)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55))))
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55))),sK5(sK2,X56,k5_relat_1(sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X55)))))),sK1) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5789])).

fof(f5789,plain,
    ( ! [X4,X5] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X4))),X5)),sK2)
        | ~ v4_pre_topc(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X4))),X5),sK1) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f547])).

fof(f15575,plain,
    ( ~ spl9_55
    | ~ spl9_19
    | spl9_626
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f15509,f5674,f15573,f185,f333])).

fof(f15573,plain,
    ( spl9_626
  <=> ! [X53,X52,X54] :
        ( v5_pre_topc(k5_relat_1(sK4,X52),sK2,X53)
        | ~ r1_tarski(X52,k2_zfmisc_1(u1_struct_0(sK1),X54))
        | ~ v4_pre_topc(k10_relat_1(X52,sK5(sK2,X53,k5_relat_1(sK4,X52))),sK1)
        | ~ v1_relat_1(X52)
        | ~ l1_pre_topc(X53)
        | ~ v1_funct_1(k5_relat_1(sK4,X52))
        | ~ v1_funct_2(k5_relat_1(sK4,X52),u1_struct_0(sK2),u1_struct_0(X53))
        | ~ m1_subset_1(k5_relat_1(sK4,X52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X53)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_626])])).

fof(f15509,plain,
    ( ! [X54,X52,X53] :
        ( v5_pre_topc(k5_relat_1(sK4,X52),sK2,X53)
        | ~ m1_subset_1(k5_relat_1(sK4,X52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X53))))
        | ~ v1_funct_2(k5_relat_1(sK4,X52),u1_struct_0(sK2),u1_struct_0(X53))
        | ~ v1_funct_1(k5_relat_1(sK4,X52))
        | ~ l1_pre_topc(X53)
        | ~ l1_pre_topc(sK2)
        | ~ v1_relat_1(X52)
        | ~ v1_relat_1(sK4)
        | ~ v4_pre_topc(k10_relat_1(X52,sK5(sK2,X53,k5_relat_1(sK4,X52))),sK1)
        | ~ r1_tarski(X52,k2_zfmisc_1(u1_struct_0(sK1),X54)) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5102,f5795])).

fof(f5795,plain,
    ( ! [X33,X31,X32] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(X31,X32)),sK2)
        | ~ v4_pre_topc(k10_relat_1(X31,X32),sK1)
        | ~ r1_tarski(X31,k2_zfmisc_1(u1_struct_0(sK1),X33)) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f543])).

fof(f15571,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_624
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15508,f5670,f15569,f206,f326])).

fof(f15569,plain,
    ( spl9_624
  <=> ! [X49,X51,X48,X50,X47] :
        ( v5_pre_topc(k5_relat_1(sK3,sK6(k10_relat_1(X47,X48))),sK0,X49)
        | ~ r1_tarski(X47,k2_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X50)),X51))
        | v1_xboole_0(k10_relat_1(X47,X48))
        | ~ v4_pre_topc(k10_relat_1(sK6(k10_relat_1(X47,X48)),sK5(sK0,X49,k5_relat_1(sK3,sK6(k10_relat_1(X47,X48))))),sK2)
        | ~ v1_relat_1(sK6(k10_relat_1(X47,X48)))
        | ~ l1_pre_topc(X49)
        | ~ v1_funct_1(k5_relat_1(sK3,sK6(k10_relat_1(X47,X48))))
        | ~ v1_funct_2(k5_relat_1(sK3,sK6(k10_relat_1(X47,X48))),u1_struct_0(sK0),u1_struct_0(X49))
        | ~ m1_subset_1(k5_relat_1(sK3,sK6(k10_relat_1(X47,X48))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X49)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_624])])).

fof(f15508,plain,
    ( ! [X47,X50,X48,X51,X49] :
        ( v5_pre_topc(k5_relat_1(sK3,sK6(k10_relat_1(X47,X48))),sK0,X49)
        | ~ m1_subset_1(k5_relat_1(sK3,sK6(k10_relat_1(X47,X48))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X49))))
        | ~ v1_funct_2(k5_relat_1(sK3,sK6(k10_relat_1(X47,X48))),u1_struct_0(sK0),u1_struct_0(X49))
        | ~ v1_funct_1(k5_relat_1(sK3,sK6(k10_relat_1(X47,X48))))
        | ~ l1_pre_topc(X49)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(sK6(k10_relat_1(X47,X48)))
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(sK6(k10_relat_1(X47,X48)),sK5(sK0,X49,k5_relat_1(sK3,sK6(k10_relat_1(X47,X48))))),sK2)
        | v1_xboole_0(k10_relat_1(X47,X48))
        | ~ r1_tarski(X47,k2_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X50)),X51)) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5690])).

fof(f5690,plain,
    ( ! [X54,X52,X50,X53,X51] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK6(k10_relat_1(X50,X51)),X52)),sK0)
        | ~ v4_pre_topc(k10_relat_1(sK6(k10_relat_1(X50,X51)),X52),sK2)
        | v1_xboole_0(k10_relat_1(X50,X51))
        | ~ r1_tarski(X50,k2_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X53)),X54)) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f1728])).

fof(f15567,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_622
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15507,f5670,f15565,f206,f326])).

fof(f15565,plain,
    ( spl9_622
  <=> ! [X46,X45] :
        ( v5_pre_topc(k5_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45)))))),sK0,X46)
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45)))))
        | ~ v4_pre_topc(k10_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45))))),sK5(sK0,X46,k5_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45)))))))),sK2)
        | ~ v1_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45))))))
        | ~ l1_pre_topc(X46)
        | ~ v1_funct_1(k5_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45)))))))
        | ~ v1_funct_2(k5_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45)))))),u1_struct_0(sK0),u1_struct_0(X46))
        | ~ m1_subset_1(k5_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45)))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X46)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_622])])).

fof(f15507,plain,
    ( ! [X45,X46] :
        ( v5_pre_topc(k5_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45)))))),sK0,X46)
        | ~ m1_subset_1(k5_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45)))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X46))))
        | ~ v1_funct_2(k5_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45)))))),u1_struct_0(sK0),u1_struct_0(X46))
        | ~ v1_funct_1(k5_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45)))))))
        | ~ l1_pre_topc(X46)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45))))))
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45))))),sK5(sK0,X46,k5_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45)))))))),sK2)
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X45))))) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5681])).

fof(f5681,plain,
    ( ! [X8,X7] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X7))))),X8)),sK0)
        | ~ v4_pre_topc(k10_relat_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X7))))),X8),sK2)
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X7))))) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f548])).

fof(f15563,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_620
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15506,f5670,f15561,f206,f326])).

fof(f15561,plain,
    ( spl9_620
  <=> ! [X44,X43] :
        ( v5_pre_topc(k5_relat_1(sK3,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43)))),sK0,X44)
        | ~ v4_pre_topc(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43))),sK5(sK0,X44,k5_relat_1(sK3,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43)))))),sK2)
        | ~ v1_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43))))
        | ~ l1_pre_topc(X44)
        | ~ v1_funct_1(k5_relat_1(sK3,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43)))))
        | ~ v1_funct_2(k5_relat_1(sK3,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43)))),u1_struct_0(sK0),u1_struct_0(X44))
        | ~ m1_subset_1(k5_relat_1(sK3,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X44)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_620])])).

fof(f15506,plain,
    ( ! [X43,X44] :
        ( v5_pre_topc(k5_relat_1(sK3,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43)))),sK0,X44)
        | ~ m1_subset_1(k5_relat_1(sK3,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X44))))
        | ~ v1_funct_2(k5_relat_1(sK3,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43)))),u1_struct_0(sK0),u1_struct_0(X44))
        | ~ v1_funct_1(k5_relat_1(sK3,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43)))))
        | ~ l1_pre_topc(X44)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43))))
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43))),sK5(sK0,X44,k5_relat_1(sK3,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X43)))))),sK2) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5680])).

fof(f5680,plain,
    ( ! [X6,X5] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X5))),X6)),sK0)
        | ~ v4_pre_topc(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X5))),X6),sK2) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f547])).

fof(f15559,plain,
    ( ~ spl9_53
    | ~ spl9_55
    | ~ spl9_25
    | ~ spl9_117
    | spl9_618
    | ~ spl9_6
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15505,f5670,f146,f15557,f1072,f206,f333,f326])).

fof(f146,plain,
    ( spl9_6
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f15505,plain,
    ( ! [X42] :
        ( v5_pre_topc(k5_relat_1(sK3,sK4),sK0,X42)
        | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X42))))
        | ~ v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(X42))
        | ~ v1_funct_1(k5_relat_1(sK3,sK4))
        | ~ l1_pre_topc(X42)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(sK4)
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(sK4,sK5(sK0,X42,k5_relat_1(sK3,sK4))),sK2) )
    | ~ spl9_6
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5679])).

fof(f5679,plain,
    ( ! [X4] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(sK4,X4)),sK0)
        | ~ v4_pre_topc(k10_relat_1(sK4,X4),sK2) )
    | ~ spl9_6
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f546])).

fof(f546,plain,
    ( ! [X11] : m1_subset_1(k10_relat_1(sK4,X11),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl9_6 ),
    inference(resolution,[],[f470,f147])).

fof(f147,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f15555,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_616
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15504,f5670,f15553,f206,f326])).

fof(f15553,plain,
    ( spl9_616
  <=> ! [X40,X36,X38,X41,X37,X39] :
        ( v5_pre_topc(k5_relat_1(sK3,k10_relat_1(X36,k10_relat_1(X37,X38))),sK0,X39)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X37)
        | ~ r1_tarski(k5_relat_1(X36,X37),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X40),X41))
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X36,k10_relat_1(X37,X38)),sK5(sK0,X39,k5_relat_1(sK3,k10_relat_1(X36,k10_relat_1(X37,X38))))),sK2)
        | ~ v1_relat_1(k10_relat_1(X36,k10_relat_1(X37,X38)))
        | ~ l1_pre_topc(X39)
        | ~ v1_funct_1(k5_relat_1(sK3,k10_relat_1(X36,k10_relat_1(X37,X38))))
        | ~ v1_funct_2(k5_relat_1(sK3,k10_relat_1(X36,k10_relat_1(X37,X38))),u1_struct_0(sK0),u1_struct_0(X39))
        | ~ m1_subset_1(k5_relat_1(sK3,k10_relat_1(X36,k10_relat_1(X37,X38))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X39)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_616])])).

fof(f15504,plain,
    ( ! [X39,X37,X41,X38,X36,X40] :
        ( v5_pre_topc(k5_relat_1(sK3,k10_relat_1(X36,k10_relat_1(X37,X38))),sK0,X39)
        | ~ m1_subset_1(k5_relat_1(sK3,k10_relat_1(X36,k10_relat_1(X37,X38))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X39))))
        | ~ v1_funct_2(k5_relat_1(sK3,k10_relat_1(X36,k10_relat_1(X37,X38))),u1_struct_0(sK0),u1_struct_0(X39))
        | ~ v1_funct_1(k5_relat_1(sK3,k10_relat_1(X36,k10_relat_1(X37,X38))))
        | ~ l1_pre_topc(X39)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(k10_relat_1(X36,k10_relat_1(X37,X38)))
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X36,k10_relat_1(X37,X38)),sK5(sK0,X39,k5_relat_1(sK3,k10_relat_1(X36,k10_relat_1(X37,X38))))),sK2)
        | ~ r1_tarski(k5_relat_1(X36,X37),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X40),X41))
        | ~ v1_relat_1(X37)
        | ~ v1_relat_1(X36) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5692])).

fof(f5692,plain,
    ( ! [X66,X64,X62,X67,X65,X63] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(k10_relat_1(X62,k10_relat_1(X63,X64)),X65)),sK0)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X62,k10_relat_1(X63,X64)),X65),sK2)
        | ~ r1_tarski(k5_relat_1(X62,X63),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X66),X67))
        | ~ v1_relat_1(X63)
        | ~ v1_relat_1(X62) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f672])).

fof(f15551,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_614
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15503,f5670,f15549,f206,f326])).

fof(f15549,plain,
    ( spl9_614
  <=> ! [X32,X34,X31,X33,X35,X30] :
        ( v5_pre_topc(k5_relat_1(sK3,k10_relat_1(X30,k10_relat_1(X31,X32))),sK0,X33)
        | ~ v1_relat_1(X30)
        | ~ v1_relat_1(X31)
        | ~ r1_tarski(k5_relat_1(X30,X31),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X34),X35))
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k5_relat_1(X30,X31),X32),sK5(sK0,X33,k5_relat_1(sK3,k10_relat_1(X30,k10_relat_1(X31,X32))))),sK2)
        | ~ v1_relat_1(k10_relat_1(X30,k10_relat_1(X31,X32)))
        | ~ l1_pre_topc(X33)
        | ~ v1_funct_1(k5_relat_1(sK3,k10_relat_1(X30,k10_relat_1(X31,X32))))
        | ~ v1_funct_2(k5_relat_1(sK3,k10_relat_1(X30,k10_relat_1(X31,X32))),u1_struct_0(sK0),u1_struct_0(X33))
        | ~ m1_subset_1(k5_relat_1(sK3,k10_relat_1(X30,k10_relat_1(X31,X32))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X33)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_614])])).

fof(f15503,plain,
    ( ! [X30,X35,X33,X31,X34,X32] :
        ( v5_pre_topc(k5_relat_1(sK3,k10_relat_1(X30,k10_relat_1(X31,X32))),sK0,X33)
        | ~ m1_subset_1(k5_relat_1(sK3,k10_relat_1(X30,k10_relat_1(X31,X32))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X33))))
        | ~ v1_funct_2(k5_relat_1(sK3,k10_relat_1(X30,k10_relat_1(X31,X32))),u1_struct_0(sK0),u1_struct_0(X33))
        | ~ v1_funct_1(k5_relat_1(sK3,k10_relat_1(X30,k10_relat_1(X31,X32))))
        | ~ l1_pre_topc(X33)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(k10_relat_1(X30,k10_relat_1(X31,X32)))
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k5_relat_1(X30,X31),X32),sK5(sK0,X33,k5_relat_1(sK3,k10_relat_1(X30,k10_relat_1(X31,X32))))),sK2)
        | ~ r1_tarski(k5_relat_1(X30,X31),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X34),X35))
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5898])).

fof(f5898,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(k10_relat_1(X0,k10_relat_1(X1,X2)),X3)),sK0)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k5_relat_1(X0,X1),X2),X3),sK2)
        | ~ r1_tarski(k5_relat_1(X0,X1),k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X4),X5))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl9_318 ),
    inference(superposition,[],[f5689,f100])).

fof(f5689,plain,
    ( ! [X47,X45,X48,X46,X49] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(k10_relat_1(X45,X46),X47)),sK0)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X45,X46),X47),sK2)
        | ~ r1_tarski(X45,k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X48),X49)) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f587])).

fof(f15547,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_612
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15502,f5670,f15545,f206,f326])).

fof(f15545,plain,
    ( spl9_612
  <=> ! [X25,X27,X29,X23,X24,X26,X28] :
        ( v5_pre_topc(k5_relat_1(sK3,k10_relat_1(k10_relat_1(X23,X24),X25)),sK0,X26)
        | ~ r1_tarski(X23,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X27),X28),X29))
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k10_relat_1(X23,X24),X25),sK5(sK0,X26,k5_relat_1(sK3,k10_relat_1(k10_relat_1(X23,X24),X25)))),sK2)
        | ~ v1_relat_1(k10_relat_1(k10_relat_1(X23,X24),X25))
        | ~ l1_pre_topc(X26)
        | ~ v1_funct_1(k5_relat_1(sK3,k10_relat_1(k10_relat_1(X23,X24),X25)))
        | ~ v1_funct_2(k5_relat_1(sK3,k10_relat_1(k10_relat_1(X23,X24),X25)),u1_struct_0(sK0),u1_struct_0(X26))
        | ~ m1_subset_1(k5_relat_1(sK3,k10_relat_1(k10_relat_1(X23,X24),X25)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X26)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_612])])).

fof(f15502,plain,
    ( ! [X28,X26,X24,X23,X29,X27,X25] :
        ( v5_pre_topc(k5_relat_1(sK3,k10_relat_1(k10_relat_1(X23,X24),X25)),sK0,X26)
        | ~ m1_subset_1(k5_relat_1(sK3,k10_relat_1(k10_relat_1(X23,X24),X25)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X26))))
        | ~ v1_funct_2(k5_relat_1(sK3,k10_relat_1(k10_relat_1(X23,X24),X25)),u1_struct_0(sK0),u1_struct_0(X26))
        | ~ v1_funct_1(k5_relat_1(sK3,k10_relat_1(k10_relat_1(X23,X24),X25)))
        | ~ l1_pre_topc(X26)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(k10_relat_1(k10_relat_1(X23,X24),X25))
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k10_relat_1(X23,X24),X25),sK5(sK0,X26,k5_relat_1(sK3,k10_relat_1(k10_relat_1(X23,X24),X25)))),sK2)
        | ~ r1_tarski(X23,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X27),X28),X29)) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5691])).

fof(f5691,plain,
    ( ! [X61,X59,X57,X60,X58,X56,X55] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(k10_relat_1(k10_relat_1(X55,X56),X57),X58)),sK0)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(k10_relat_1(X55,X56),X57),X58),sK2)
        | ~ r1_tarski(X55,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X59),X60),X61)) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f668])).

fof(f15543,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_610
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15501,f5670,f15541,f206,f326])).

fof(f15541,plain,
    ( spl9_610
  <=> ! [X20,X22,X19,X21] :
        ( v5_pre_topc(k5_relat_1(sK3,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21)),sK0,X22)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21),sK5(sK0,X22,k5_relat_1(sK3,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21)))),sK2)
        | ~ v1_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21))
        | ~ l1_pre_topc(X22)
        | ~ v1_funct_1(k5_relat_1(sK3,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21)))
        | ~ v1_funct_2(k5_relat_1(sK3,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21)),u1_struct_0(sK0),u1_struct_0(X22))
        | ~ m1_subset_1(k5_relat_1(sK3,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_610])])).

fof(f15501,plain,
    ( ! [X21,X19,X22,X20] :
        ( v5_pre_topc(k5_relat_1(sK3,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21)),sK0,X22)
        | ~ m1_subset_1(k5_relat_1(sK3,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X22))))
        | ~ v1_funct_2(k5_relat_1(sK3,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21)),u1_struct_0(sK0),u1_struct_0(X22))
        | ~ v1_funct_1(k5_relat_1(sK3,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21)))
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21))
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21),sK5(sK0,X22,k5_relat_1(sK3,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X19),X20))),X21)))),sK2) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5682])).

fof(f5682,plain,
    ( ! [X12,X10,X11,X9] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X9),X10))),X11),X12)),sK0)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X9),X10))),X11),X12),sK2) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f580])).

fof(f15539,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_608
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15500,f5670,f15537,f206,f326])).

fof(f15537,plain,
    ( spl9_608
  <=> ! [X16,X18,X15,X17,X14] :
        ( v5_pre_topc(k5_relat_1(sK3,k10_relat_1(X14,X15)),sK0,X16)
        | ~ r1_tarski(X14,k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X17),X18))
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X14,X15),sK5(sK0,X16,k5_relat_1(sK3,k10_relat_1(X14,X15)))),sK2)
        | ~ v1_relat_1(k10_relat_1(X14,X15))
        | ~ l1_pre_topc(X16)
        | ~ v1_funct_1(k5_relat_1(sK3,k10_relat_1(X14,X15)))
        | ~ v1_funct_2(k5_relat_1(sK3,k10_relat_1(X14,X15)),u1_struct_0(sK0),u1_struct_0(X16))
        | ~ m1_subset_1(k5_relat_1(sK3,k10_relat_1(X14,X15)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X16)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_608])])).

fof(f15500,plain,
    ( ! [X14,X17,X15,X18,X16] :
        ( v5_pre_topc(k5_relat_1(sK3,k10_relat_1(X14,X15)),sK0,X16)
        | ~ m1_subset_1(k5_relat_1(sK3,k10_relat_1(X14,X15)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X16))))
        | ~ v1_funct_2(k5_relat_1(sK3,k10_relat_1(X14,X15)),u1_struct_0(sK0),u1_struct_0(X16))
        | ~ v1_funct_1(k5_relat_1(sK3,k10_relat_1(X14,X15)))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(k10_relat_1(X14,X15))
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(k10_relat_1(X14,X15),sK5(sK0,X16,k5_relat_1(sK3,k10_relat_1(X14,X15)))),sK2)
        | ~ r1_tarski(X14,k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X17),X18)) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5689])).

fof(f15535,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_606
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15499,f5670,f15533,f206,f326])).

fof(f15533,plain,
    ( spl9_606
  <=> ! [X9,X11,X13,X8,X10,X12] :
        ( v5_pre_topc(k5_relat_1(sK3,k5_relat_1(X8,X9)),sK0,X10)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X11)))
        | ~ v1_funct_1(X9)
        | ~ v4_pre_topc(k10_relat_1(k5_relat_1(X8,X9),sK5(sK0,X10,k5_relat_1(sK3,k5_relat_1(X8,X9)))),sK2)
        | ~ v1_relat_1(k5_relat_1(X8,X9))
        | ~ l1_pre_topc(X10)
        | ~ v1_funct_1(k5_relat_1(sK3,k5_relat_1(X8,X9)))
        | ~ v1_funct_2(k5_relat_1(sK3,k5_relat_1(X8,X9)),u1_struct_0(sK0),u1_struct_0(X10))
        | ~ m1_subset_1(k5_relat_1(sK3,k5_relat_1(X8,X9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X10)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_606])])).

fof(f15499,plain,
    ( ! [X12,X10,X8,X13,X11,X9] :
        ( v5_pre_topc(k5_relat_1(sK3,k5_relat_1(X8,X9)),sK0,X10)
        | ~ m1_subset_1(k5_relat_1(sK3,k5_relat_1(X8,X9)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X10))))
        | ~ v1_funct_2(k5_relat_1(sK3,k5_relat_1(X8,X9)),u1_struct_0(sK0),u1_struct_0(X10))
        | ~ v1_funct_1(k5_relat_1(sK3,k5_relat_1(X8,X9)))
        | ~ l1_pre_topc(X10)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(k5_relat_1(X8,X9))
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(k5_relat_1(X8,X9),sK5(sK0,X10,k5_relat_1(sK3,k5_relat_1(X8,X9)))),sK2)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X11)))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5688])).

fof(f5688,plain,
    ( ! [X39,X43,X41,X44,X42,X40] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(k5_relat_1(X39,X40),X41)),sK0)
        | ~ v4_pre_topc(k10_relat_1(k5_relat_1(X39,X40),X41),sK2)
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X42)))
        | ~ v1_funct_1(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f2763])).

fof(f15531,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_604
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15498,f5670,f15529,f206,f326])).

fof(f15529,plain,
    ( spl9_604
  <=> ! [X3,X5,X7,X4,X6] :
        ( v5_pre_topc(k5_relat_1(sK3,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6)),sK0,X7)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4)))
        | ~ v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6),sK5(sK0,X7,k5_relat_1(sK3,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6)))),sK2)
        | ~ v1_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6))
        | ~ l1_pre_topc(X7)
        | ~ v1_funct_1(k5_relat_1(sK3,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6)))
        | ~ v1_funct_2(k5_relat_1(sK3,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6)),u1_struct_0(sK0),u1_struct_0(X7))
        | ~ m1_subset_1(k5_relat_1(sK3,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_604])])).

fof(f15498,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( v5_pre_topc(k5_relat_1(sK3,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6)),sK0,X7)
        | ~ m1_subset_1(k5_relat_1(sK3,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X7))))
        | ~ v1_funct_2(k5_relat_1(sK3,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6)),u1_struct_0(sK0),u1_struct_0(X7))
        | ~ v1_funct_1(k5_relat_1(sK3,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6)))
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6))
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6),sK5(sK0,X7,k5_relat_1(sK3,k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4,X5,X6)))),sK2)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X3),X4))) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5685])).

fof(f5685,plain,
    ( ! [X30,X28,X31,X29,X27] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X27),X28,X29,X30),X31)),sK0)
        | ~ v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK2),X27),X28,X29,X30),X31),sK2)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X27),X28))) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f544])).

fof(f15527,plain,
    ( ~ spl9_53
    | ~ spl9_25
    | spl9_602
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f15497,f5670,f15525,f206,f326])).

fof(f15525,plain,
    ( spl9_602
  <=> ! [X1,X0,X2] :
        ( v5_pre_topc(k5_relat_1(sK3,X0),sK0,X1)
        | ~ r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK2),X2))
        | ~ v4_pre_topc(k10_relat_1(X0,sK5(sK0,X1,k5_relat_1(sK3,X0))),sK2)
        | ~ v1_relat_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(k5_relat_1(sK3,X0))
        | ~ v1_funct_2(k5_relat_1(sK3,X0),u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(k5_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_602])])).

fof(f15497,plain,
    ( ! [X2,X0,X1] :
        ( v5_pre_topc(k5_relat_1(sK3,X0),sK0,X1)
        | ~ m1_subset_1(k5_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(k5_relat_1(sK3,X0),u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(k5_relat_1(sK3,X0))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK3)
        | ~ v4_pre_topc(k10_relat_1(X0,sK5(sK0,X1,k5_relat_1(sK3,X0))),sK2)
        | ~ r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK2),X2)) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5102,f5686])).

fof(f5686,plain,
    ( ! [X33,X34,X32] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(X32,X33)),sK0)
        | ~ v4_pre_topc(k10_relat_1(X32,X33),sK2)
        | ~ r1_tarski(X32,k2_zfmisc_1(u1_struct_0(sK2),X34)) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f543])).

fof(f15377,plain,
    ( ~ spl9_12
    | ~ spl9_582 ),
    inference(avatar_contradiction_clause,[],[f15375])).

fof(f15375,plain,
    ( $false
    | ~ spl9_12
    | ~ spl9_582 ),
    inference(resolution,[],[f15334,f168])).

fof(f15334,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | ~ spl9_582 ),
    inference(avatar_component_clause,[],[f15333])).

fof(f15374,plain,
    ( ~ spl9_6
    | ~ spl9_578 ),
    inference(avatar_contradiction_clause,[],[f15372])).

fof(f15372,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_578 ),
    inference(resolution,[],[f15325,f147])).

fof(f15325,plain,
    ( ! [X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ spl9_578 ),
    inference(avatar_component_clause,[],[f15324])).

fof(f15370,plain,
    ( ~ spl9_19
    | ~ spl9_11
    | spl9_598
    | spl9_600
    | ~ spl9_290 ),
    inference(avatar_split_clause,[],[f15315,f4686,f15368,f15365,f157,f185])).

fof(f15365,plain,
    ( spl9_598
  <=> ! [X40] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X40))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_598])])).

fof(f15368,plain,
    ( spl9_600
  <=> ! [X42,X41,X39] :
        ( ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(sK1),u1_struct_0(X41))
        | ~ r1_tarski(X39,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X41)))
        | ~ l1_pre_topc(X41)
        | ~ v1_funct_1(k5_relat_1(sK4,X39))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X42,u1_struct_0(X41))))
        | v5_pre_topc(k5_relat_1(sK4,X39),sK2,X41)
        | v4_pre_topc(sK5(sK2,X41,k5_relat_1(sK4,X39)),X41) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_600])])).

fof(f4686,plain,
    ( spl9_290
  <=> ! [X148,X149] :
        ( ~ v1_funct_2(X148,u1_struct_0(sK1),X149)
        | ~ r1_tarski(X148,k2_zfmisc_1(u1_struct_0(sK1),X149))
        | v1_funct_2(k5_relat_1(sK4,X148),u1_struct_0(sK2),X149)
        | ~ v1_funct_1(X148) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_290])])).

fof(f15315,plain,
    ( ! [X39,X41,X42,X40] :
        ( ~ v1_funct_1(X39)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X40)))
        | ~ v1_funct_1(sK4)
        | v4_pre_topc(sK5(sK2,X41,k5_relat_1(sK4,X39)),X41)
        | v5_pre_topc(k5_relat_1(sK4,X39),sK2,X41)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X42,u1_struct_0(X41))))
        | ~ v1_funct_1(k5_relat_1(sK4,X39))
        | ~ l1_pre_topc(X41)
        | ~ l1_pre_topc(sK2)
        | ~ r1_tarski(X39,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X41)))
        | ~ v1_funct_2(X39,u1_struct_0(sK1),u1_struct_0(X41)) )
    | ~ spl9_290 ),
    inference(duplicate_literal_removal,[],[f15300])).

fof(f15300,plain,
    ( ! [X39,X41,X42,X40] :
        ( ~ v1_funct_1(X39)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X40)))
        | ~ v1_funct_1(sK4)
        | v4_pre_topc(sK5(sK2,X41,k5_relat_1(sK4,X39)),X41)
        | v5_pre_topc(k5_relat_1(sK4,X39),sK2,X41)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X42,u1_struct_0(X41))))
        | ~ v1_funct_1(k5_relat_1(sK4,X39))
        | ~ l1_pre_topc(X41)
        | ~ l1_pre_topc(sK2)
        | ~ r1_tarski(X39,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X41)))
        | ~ v1_funct_2(X39,u1_struct_0(sK1),u1_struct_0(X41))
        | ~ v1_funct_1(X39) )
    | ~ spl9_290 ),
    inference(resolution,[],[f2781,f4687])).

fof(f4687,plain,
    ( ! [X149,X148] :
        ( v1_funct_2(k5_relat_1(sK4,X148),u1_struct_0(sK2),X149)
        | ~ r1_tarski(X148,k2_zfmisc_1(u1_struct_0(sK1),X149))
        | ~ v1_funct_2(X148,u1_struct_0(sK1),X149)
        | ~ v1_funct_1(X148) )
    | ~ spl9_290 ),
    inference(avatar_component_clause,[],[f4686])).

fof(f15363,plain,
    ( ~ spl9_25
    | ~ spl9_17
    | spl9_582
    | spl9_596
    | ~ spl9_286 ),
    inference(avatar_split_clause,[],[f15316,f4676,f15361,f15333,f178,f206])).

fof(f15361,plain,
    ( spl9_596
  <=> ! [X38,X35,X37] :
        ( ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(sK2),u1_struct_0(X37))
        | ~ r1_tarski(X35,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X37)))
        | ~ l1_pre_topc(X37)
        | ~ v1_funct_1(k5_relat_1(sK3,X35))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X38,u1_struct_0(X37))))
        | v5_pre_topc(k5_relat_1(sK3,X35),sK0,X37)
        | v4_pre_topc(sK5(sK0,X37,k5_relat_1(sK3,X35)),X37) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_596])])).

fof(f4676,plain,
    ( spl9_286
  <=> ! [X147,X146] :
        ( ~ v1_funct_2(X146,u1_struct_0(sK2),X147)
        | ~ r1_tarski(X146,k2_zfmisc_1(u1_struct_0(sK2),X147))
        | v1_funct_2(k5_relat_1(sK3,X146),u1_struct_0(sK0),X147)
        | ~ v1_funct_1(X146) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_286])])).

fof(f15316,plain,
    ( ! [X37,X35,X38,X36] :
        ( ~ v1_funct_1(X35)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X36)))
        | ~ v1_funct_1(sK3)
        | v4_pre_topc(sK5(sK0,X37,k5_relat_1(sK3,X35)),X37)
        | v5_pre_topc(k5_relat_1(sK3,X35),sK0,X37)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X38,u1_struct_0(X37))))
        | ~ v1_funct_1(k5_relat_1(sK3,X35))
        | ~ l1_pre_topc(X37)
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X35,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X37)))
        | ~ v1_funct_2(X35,u1_struct_0(sK2),u1_struct_0(X37)) )
    | ~ spl9_286 ),
    inference(duplicate_literal_removal,[],[f15299])).

fof(f15299,plain,
    ( ! [X37,X35,X38,X36] :
        ( ~ v1_funct_1(X35)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X36)))
        | ~ v1_funct_1(sK3)
        | v4_pre_topc(sK5(sK0,X37,k5_relat_1(sK3,X35)),X37)
        | v5_pre_topc(k5_relat_1(sK3,X35),sK0,X37)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X38,u1_struct_0(X37))))
        | ~ v1_funct_1(k5_relat_1(sK3,X35))
        | ~ l1_pre_topc(X37)
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X35,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X37)))
        | ~ v1_funct_2(X35,u1_struct_0(sK2),u1_struct_0(X37))
        | ~ v1_funct_1(X35) )
    | ~ spl9_286 ),
    inference(resolution,[],[f2781,f4677])).

fof(f4677,plain,
    ( ! [X146,X147] :
        ( v1_funct_2(k5_relat_1(sK3,X146),u1_struct_0(sK0),X147)
        | ~ r1_tarski(X146,k2_zfmisc_1(u1_struct_0(sK2),X147))
        | ~ v1_funct_2(X146,u1_struct_0(sK2),X147)
        | ~ v1_funct_1(X146) )
    | ~ spl9_286 ),
    inference(avatar_component_clause,[],[f4676])).

fof(f15359,plain,
    ( ~ spl9_23
    | spl9_578
    | spl9_594
    | ~ spl9_11
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f15317,f1978,f157,f15357,f15324,f199])).

fof(f15357,plain,
    ( spl9_594
  <=> ! [X34,X29,X31,X33,X28,X30] :
        ( ~ m1_subset_1(k5_relat_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),X31)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X34,u1_struct_0(sK2))))
        | ~ v1_funct_2(k5_relat_1(X28,X29),u1_struct_0(X30),u1_struct_0(sK2))
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),X33)))
        | ~ v1_funct_1(X29)
        | ~ l1_pre_topc(X30)
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(X28,X29),sK4))
        | v5_pre_topc(k5_relat_1(k5_relat_1(X28,X29),sK4),X30,sK1)
        | v4_pre_topc(sK5(X30,sK1,k5_relat_1(k5_relat_1(X28,X29),sK4)),sK1)
        | ~ v1_funct_1(k5_relat_1(X28,X29)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_594])])).

fof(f15317,plain,
    ( ! [X30,X28,X33,X31,X29,X34,X32] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(k5_relat_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),X31)))
        | ~ v1_funct_1(k5_relat_1(X28,X29))
        | v4_pre_topc(sK5(X30,sK1,k5_relat_1(k5_relat_1(X28,X29),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(k5_relat_1(X28,X29),sK4),X30,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X32,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(X28,X29),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X30)
        | ~ v1_funct_1(X29)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),X33)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(k5_relat_1(X28,X29),u1_struct_0(X30),u1_struct_0(sK2))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X34,u1_struct_0(sK2)))) )
    | ~ spl9_126 ),
    inference(duplicate_literal_removal,[],[f15298])).

fof(f15298,plain,
    ( ! [X30,X28,X33,X31,X29,X34,X32] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(k5_relat_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),X31)))
        | ~ v1_funct_1(k5_relat_1(X28,X29))
        | v4_pre_topc(sK5(X30,sK1,k5_relat_1(k5_relat_1(X28,X29),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(k5_relat_1(X28,X29),sK4),X30,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X32,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(X28,X29),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X30)
        | ~ v1_funct_1(X29)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),X33)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_1(k5_relat_1(X28,X29))
        | ~ v1_funct_2(k5_relat_1(X28,X29),u1_struct_0(X30),u1_struct_0(sK2))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X34,u1_struct_0(sK2)))) )
    | ~ spl9_126 ),
    inference(resolution,[],[f2781,f2779])).

fof(f2779,plain,
    ( ! [X142,X140,X143,X141,X139] :
        ( v1_funct_2(k5_relat_1(k5_relat_1(X141,X139),sK4),X142,u1_struct_0(sK1))
        | ~ v1_funct_1(X139)
        | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(X142,X143)))
        | ~ v1_funct_1(X141)
        | ~ v1_funct_1(k5_relat_1(X141,X139))
        | ~ v1_funct_2(k5_relat_1(X141,X139),X142,u1_struct_0(sK2))
        | ~ m1_subset_1(X139,k1_zfmisc_1(k2_zfmisc_1(X140,u1_struct_0(sK2)))) )
    | ~ spl9_126 ),
    inference(resolution,[],[f833,f1979])).

fof(f15355,plain,
    ( ~ spl9_23
    | spl9_578
    | spl9_592
    | ~ spl9_11
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f15318,f1978,f157,f15353,f15324,f199])).

fof(f15353,plain,
    ( spl9_592
  <=> ! [X22,X25,X27,X23,X24] :
        ( ~ m1_subset_1(k10_relat_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),X25)))
        | ~ r1_tarski(X22,k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK2)),X27))
        | ~ v1_funct_2(k10_relat_1(X22,X23),u1_struct_0(X24),u1_struct_0(sK2))
        | ~ l1_pre_topc(X24)
        | ~ v1_funct_1(k5_relat_1(k10_relat_1(X22,X23),sK4))
        | v5_pre_topc(k5_relat_1(k10_relat_1(X22,X23),sK4),X24,sK1)
        | v4_pre_topc(sK5(X24,sK1,k5_relat_1(k10_relat_1(X22,X23),sK4)),sK1)
        | ~ v1_funct_1(k10_relat_1(X22,X23)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_592])])).

fof(f15318,plain,
    ( ! [X26,X24,X23,X27,X25,X22] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(k10_relat_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),X25)))
        | ~ v1_funct_1(k10_relat_1(X22,X23))
        | v4_pre_topc(sK5(X24,sK1,k5_relat_1(k10_relat_1(X22,X23),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(k10_relat_1(X22,X23),sK4),X24,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X26,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(k10_relat_1(X22,X23),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X24)
        | ~ v1_funct_2(k10_relat_1(X22,X23),u1_struct_0(X24),u1_struct_0(sK2))
        | ~ r1_tarski(X22,k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK2)),X27)) )
    | ~ spl9_126 ),
    inference(duplicate_literal_removal,[],[f15297])).

fof(f15297,plain,
    ( ! [X26,X24,X23,X27,X25,X22] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(k10_relat_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),X25)))
        | ~ v1_funct_1(k10_relat_1(X22,X23))
        | v4_pre_topc(sK5(X24,sK1,k5_relat_1(k10_relat_1(X22,X23),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(k10_relat_1(X22,X23),sK4),X24,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X26,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(k10_relat_1(X22,X23),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X24)
        | ~ v1_funct_2(k10_relat_1(X22,X23),u1_struct_0(X24),u1_struct_0(sK2))
        | ~ v1_funct_1(k10_relat_1(X22,X23))
        | ~ r1_tarski(X22,k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(sK2)),X27)) )
    | ~ spl9_126 ),
    inference(resolution,[],[f2781,f2019])).

fof(f2019,plain,
    ( ! [X37,X35,X38,X36] :
        ( v1_funct_2(k5_relat_1(k10_relat_1(X35,X36),sK4),X37,u1_struct_0(sK1))
        | ~ v1_funct_2(k10_relat_1(X35,X36),X37,u1_struct_0(sK2))
        | ~ v1_funct_1(k10_relat_1(X35,X36))
        | ~ r1_tarski(X35,k2_zfmisc_1(k2_zfmisc_1(X37,u1_struct_0(sK2)),X38)) )
    | ~ spl9_126 ),
    inference(resolution,[],[f1979,f543])).

fof(f15351,plain,
    ( ~ spl9_23
    | spl9_578
    | spl9_590
    | ~ spl9_11
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f15319,f1978,f157,f15349,f15324,f199])).

fof(f15349,plain,
    ( spl9_590
  <=> ! [X18,X20,X19] :
        ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),X20)))
        | ~ r1_tarski(X18,k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK2)))
        | ~ v1_funct_2(X18,u1_struct_0(X19),u1_struct_0(sK2))
        | ~ l1_pre_topc(X19)
        | ~ v1_funct_1(k5_relat_1(X18,sK4))
        | v5_pre_topc(k5_relat_1(X18,sK4),X19,sK1)
        | v4_pre_topc(sK5(X19,sK1,k5_relat_1(X18,sK4)),sK1)
        | ~ v1_funct_1(X18) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_590])])).

fof(f15319,plain,
    ( ! [X21,X19,X20,X18] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),X20)))
        | ~ v1_funct_1(X18)
        | v4_pre_topc(sK5(X19,sK1,k5_relat_1(X18,sK4)),sK1)
        | v5_pre_topc(k5_relat_1(X18,sK4),X19,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X21,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(X18,sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X19)
        | ~ v1_funct_2(X18,u1_struct_0(X19),u1_struct_0(sK2))
        | ~ r1_tarski(X18,k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK2))) )
    | ~ spl9_126 ),
    inference(duplicate_literal_removal,[],[f15296])).

fof(f15296,plain,
    ( ! [X21,X19,X20,X18] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),X20)))
        | ~ v1_funct_1(X18)
        | v4_pre_topc(sK5(X19,sK1,k5_relat_1(X18,sK4)),sK1)
        | v5_pre_topc(k5_relat_1(X18,sK4),X19,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X21,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(X18,sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X19)
        | ~ v1_funct_2(X18,u1_struct_0(X19),u1_struct_0(sK2))
        | ~ v1_funct_1(X18)
        | ~ r1_tarski(X18,k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(sK2))) )
    | ~ spl9_126 ),
    inference(resolution,[],[f2781,f2011])).

fof(f2011,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k5_relat_1(X0,sK4),X1,u1_struct_0(sK1))
        | ~ v1_funct_2(X0,X1,u1_struct_0(sK2))
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(X0,k2_zfmisc_1(X1,u1_struct_0(sK2))) )
    | ~ spl9_126 ),
    inference(resolution,[],[f1979,f106])).

fof(f15347,plain,
    ( ~ spl9_23
    | spl9_578
    | spl9_588
    | ~ spl9_11
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f15320,f1978,f157,f15345,f15324,f199])).

fof(f15345,plain,
    ( spl9_588
  <=> ! [X16,X11,X13,X15,X12,X14] :
        ( ~ m1_subset_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),X16)))
        | ~ v1_funct_1(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),X12)))
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,u1_struct_0(sK2))))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),u1_struct_0(X11),u1_struct_0(sK2))
        | ~ l1_pre_topc(X11)
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),sK4))
        | v5_pre_topc(k5_relat_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),sK4),X11,sK1)
        | v4_pre_topc(sK5(X11,sK1,k5_relat_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),sK4)),sK1)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_588])])).

fof(f15320,plain,
    ( ! [X14,X12,X17,X15,X13,X11,X16] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),X16)))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15))
        | v4_pre_topc(sK5(X11,sK1,k5_relat_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),sK4),X11,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X17,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X11)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),u1_struct_0(X11),u1_struct_0(sK2))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,u1_struct_0(sK2))))
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),X12)))
        | ~ v1_funct_1(X14) )
    | ~ spl9_126 ),
    inference(duplicate_literal_removal,[],[f15295])).

fof(f15295,plain,
    ( ! [X14,X12,X17,X15,X13,X11,X16] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),X16)))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15))
        | v4_pre_topc(sK5(X11,sK1,k5_relat_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),sK4),X11,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X17,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X11)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15),u1_struct_0(X11),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X11),X12,X13,u1_struct_0(sK2),X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,u1_struct_0(sK2))))
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),X12)))
        | ~ v1_funct_1(X14) )
    | ~ spl9_126 ),
    inference(resolution,[],[f2781,f2012])).

fof(f2012,plain,
    ( ! [X6,X4,X2,X5,X3] :
        ( v1_funct_2(k5_relat_1(k1_partfun1(X2,X3,X4,u1_struct_0(sK2),X5,X6),sK4),X2,u1_struct_0(sK1))
        | ~ v1_funct_2(k1_partfun1(X2,X3,X4,u1_struct_0(sK2),X5,X6),X2,u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(X2,X3,X4,u1_struct_0(sK2),X5,X6))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(sK2))))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5) )
    | ~ spl9_126 ),
    inference(resolution,[],[f1979,f118])).

fof(f15343,plain,
    ( ~ spl9_23
    | spl9_578
    | spl9_586
    | ~ spl9_11
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f15321,f1978,f157,f15341,f15324,f199])).

fof(f15341,plain,
    ( spl9_586
  <=> ! [X9,X5,X7,X8,X6] :
        ( ~ m1_subset_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),X9)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6)))
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),u1_struct_0(X5),u1_struct_0(sK2))
        | ~ l1_pre_topc(X5)
        | ~ v1_funct_1(k5_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),sK4))
        | v5_pre_topc(k5_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),sK4),X5,sK1)
        | v4_pre_topc(sK5(X5,sK1,k5_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),sK4)),sK1)
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_586])])).

fof(f15321,plain,
    ( ! [X6,X10,X8,X7,X5,X9] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),X9)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8))
        | v4_pre_topc(sK5(X5,sK1,k5_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),sK4),X5,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X10,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X5)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),u1_struct_0(X5),u1_struct_0(sK2))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6))) )
    | ~ spl9_126 ),
    inference(duplicate_literal_removal,[],[f15294])).

fof(f15294,plain,
    ( ! [X6,X10,X8,X7,X5,X9] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),X9)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8))
        | v4_pre_topc(sK5(X5,sK1,k5_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),sK4),X5,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X10,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X5)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8),u1_struct_0(X5),u1_struct_0(sK2))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6,X7,X8))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK2)),X6))) )
    | ~ spl9_126 ),
    inference(resolution,[],[f2781,f2013])).

fof(f2013,plain,
    ( ! [X10,X8,X7,X9] :
        ( v1_funct_2(k5_relat_1(k8_relset_1(k2_zfmisc_1(X7,u1_struct_0(sK2)),X8,X9,X10),sK4),X7,u1_struct_0(sK1))
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(X7,u1_struct_0(sK2)),X8,X9,X10),X7,u1_struct_0(sK2))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(X7,u1_struct_0(sK2)),X8,X9,X10))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,u1_struct_0(sK2)),X8))) )
    | ~ spl9_126 ),
    inference(resolution,[],[f1979,f112])).

fof(f15339,plain,
    ( ~ spl9_23
    | spl9_578
    | spl9_584
    | ~ spl9_11
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f15322,f1978,f157,f15337,f15324,f199])).

fof(f15337,plain,
    ( spl9_584
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X3)))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),u1_struct_0(X2),u1_struct_0(sK2))
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),sK4))
        | v5_pre_topc(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),sK4),X2,sK1)
        | v4_pre_topc(sK5(X2,sK1,k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),sK4)),sK1)
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_584])])).

fof(f15322,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X3)))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))))
        | v4_pre_topc(sK5(X2,sK1,k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),sK4),X2,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),u1_struct_0(X2),u1_struct_0(sK2)) )
    | ~ spl9_126 ),
    inference(duplicate_literal_removal,[],[f15293])).

fof(f15293,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),X3)))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))))
        | v4_pre_topc(sK5(X2,sK1,k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),sK4)),sK1)
        | v5_pre_topc(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),sK4),X2,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X4,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))),u1_struct_0(X2),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))) )
    | ~ spl9_126 ),
    inference(resolution,[],[f2781,f2025])).

fof(f2025,plain,
    ( ! [X64] :
        ( v1_funct_2(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X64,u1_struct_0(sK2)))),sK4),X64,u1_struct_0(sK1))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(X64,u1_struct_0(sK2)))),X64,u1_struct_0(sK2))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X64,u1_struct_0(sK2))))) )
    | ~ spl9_126 ),
    inference(resolution,[],[f1979,f99])).

fof(f15335,plain,
    ( ~ spl9_25
    | ~ spl9_23
    | ~ spl9_117
    | spl9_578
    | spl9_100
    | spl9_580
    | ~ spl9_17
    | spl9_582
    | ~ spl9_11
    | ~ spl9_130 ),
    inference(avatar_split_clause,[],[f15292,f2036,f157,f15333,f178,f15330,f684,f15324,f1072,f199,f206])).

fof(f15330,plain,
    ( spl9_580
  <=> v4_pre_topc(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_580])])).

fof(f2036,plain,
    ( spl9_130
  <=> v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).

fof(f15292,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ v1_funct_1(sK3)
        | v4_pre_topc(sK5(sK0,sK1,k5_relat_1(sK3,sK4)),sK1)
        | v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(sK3,sK4))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl9_130 ),
    inference(resolution,[],[f2781,f2037])).

fof(f2037,plain,
    ( v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_130 ),
    inference(avatar_component_clause,[],[f2036])).

fof(f13326,plain,
    ( spl9_576
    | ~ spl9_11
    | ~ spl9_6
    | ~ spl9_156 ),
    inference(avatar_split_clause,[],[f13308,f2940,f146,f157,f13324])).

fof(f13324,plain,
    ( spl9_576
  <=> ! [X258,X256,X257] :
        ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,X256)))
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258))
        | ~ v1_funct_1(X256) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_576])])).

fof(f2940,plain,
    ( spl9_156
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168))
        | v1_relat_1(k5_relat_1(sK4,X166)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_156])])).

fof(f13308,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(sK4)
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,X256)))
        | ~ v1_funct_1(X256)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258)) )
    | ~ spl9_6
    | ~ spl9_156 ),
    inference(resolution,[],[f13161,f147])).

fof(f13161,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3)
        | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_156 ),
    inference(resolution,[],[f13160,f106])).

fof(f13160,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3) )
    | ~ spl9_156 ),
    inference(duplicate_literal_removal,[],[f13157])).

fof(f13157,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_156 ),
    inference(resolution,[],[f13156,f117])).

fof(f13156,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X4,X5)))
        | ~ v1_funct_1(X5) )
    | ~ spl9_156 ),
    inference(duplicate_literal_removal,[],[f13155])).

fof(f13155,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(X4,X5)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_156 ),
    inference(superposition,[],[f3142,f116])).

fof(f3142,plain,
    ( ! [X101,X99,X97,X100,X98,X96] :
        ( v1_relat_1(k5_relat_1(sK4,k1_partfun1(X98,X99,X100,X101,X97,X96)))
        | ~ m1_subset_1(X97,k1_zfmisc_1(k2_zfmisc_1(X98,X99)))
        | ~ v1_funct_1(X97)
        | ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X100,X101)))
        | ~ v1_funct_1(k1_partfun1(X98,X99,X100,X101,X97,X96))
        | ~ v1_funct_1(X96) )
    | ~ spl9_156 ),
    inference(resolution,[],[f830,f2941])).

fof(f2941,plain,
    ( ! [X167,X166,X168] :
        ( ~ r1_tarski(X166,k2_zfmisc_1(X167,X168))
        | ~ v1_funct_1(X166)
        | v1_relat_1(k5_relat_1(sK4,X166)) )
    | ~ spl9_156 ),
    inference(avatar_component_clause,[],[f2940])).

fof(f830,plain,(
    ! [X80,X83,X81,X79,X84,X82] :
      ( r1_tarski(k1_partfun1(X83,X84,X80,X81,X82,X79),k2_zfmisc_1(X83,X81))
      | ~ v1_funct_1(X79)
      | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X83,X84)))
      | ~ v1_funct_1(X82)
      | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X80,X81))) ) ),
    inference(resolution,[],[f118,f105])).

fof(f13322,plain,
    ( spl9_574
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_156 ),
    inference(avatar_split_clause,[],[f13307,f2940,f167,f178,f13320])).

fof(f13320,plain,
    ( spl9_574
  <=> ! [X254,X253,X255] :
        ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,X253)))
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255))
        | ~ v1_funct_1(X253) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_574])])).

fof(f13307,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(sK3)
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,X253)))
        | ~ v1_funct_1(X253)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255)) )
    | ~ spl9_12
    | ~ spl9_156 ),
    inference(resolution,[],[f13161,f168])).

fof(f13205,plain,
    ( ~ spl9_11
    | spl9_572
    | ~ spl9_6
    | ~ spl9_156 ),
    inference(avatar_split_clause,[],[f13187,f2940,f146,f13203,f157])).

fof(f13203,plain,
    ( spl9_572
  <=> ! [X258,X256,X257] :
        ( ~ v1_funct_1(X256)
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X256,sK4)))
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_572])])).

fof(f13187,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(X256)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258)))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X256,sK4)))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_6
    | ~ spl9_156 ),
    inference(resolution,[],[f13160,f147])).

fof(f13201,plain,
    ( ~ spl9_17
    | spl9_570
    | ~ spl9_12
    | ~ spl9_156 ),
    inference(avatar_split_clause,[],[f13186,f2940,f167,f13199,f178])).

fof(f13199,plain,
    ( spl9_570
  <=> ! [X254,X253,X255] :
        ( ~ v1_funct_1(X253)
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X253,sK3)))
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_570])])).

fof(f13186,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(X253)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255)))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X253,sK3)))
        | ~ v1_funct_1(sK3) )
    | ~ spl9_12
    | ~ spl9_156 ),
    inference(resolution,[],[f13160,f168])).

fof(f13029,plain,
    ( spl9_568
    | ~ spl9_11
    | ~ spl9_6
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f13011,f2936,f146,f157,f13027])).

fof(f13027,plain,
    ( spl9_568
  <=> ! [X258,X256,X257] :
        ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,X256)))
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258))
        | ~ v1_funct_1(X256) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_568])])).

fof(f2936,plain,
    ( spl9_154
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165))
        | v1_relat_1(k5_relat_1(sK3,X163)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_154])])).

fof(f13011,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(sK4)
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,X256)))
        | ~ v1_funct_1(X256)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258)) )
    | ~ spl9_6
    | ~ spl9_154 ),
    inference(resolution,[],[f12861,f147])).

fof(f12861,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3)
        | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_154 ),
    inference(resolution,[],[f12860,f106])).

fof(f12860,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3) )
    | ~ spl9_154 ),
    inference(duplicate_literal_removal,[],[f12857])).

fof(f12857,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_154 ),
    inference(resolution,[],[f12856,f117])).

fof(f12856,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X4,X5)))
        | ~ v1_funct_1(X5) )
    | ~ spl9_154 ),
    inference(duplicate_literal_removal,[],[f12855])).

fof(f12855,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(X4,X5)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_154 ),
    inference(superposition,[],[f3141,f116])).

fof(f3141,plain,
    ( ! [X94,X92,X90,X95,X93,X91] :
        ( v1_relat_1(k5_relat_1(sK3,k1_partfun1(X92,X93,X94,X95,X91,X90)))
        | ~ m1_subset_1(X91,k1_zfmisc_1(k2_zfmisc_1(X92,X93)))
        | ~ v1_funct_1(X91)
        | ~ m1_subset_1(X90,k1_zfmisc_1(k2_zfmisc_1(X94,X95)))
        | ~ v1_funct_1(k1_partfun1(X92,X93,X94,X95,X91,X90))
        | ~ v1_funct_1(X90) )
    | ~ spl9_154 ),
    inference(resolution,[],[f830,f2937])).

fof(f2937,plain,
    ( ! [X165,X163,X164] :
        ( ~ r1_tarski(X163,k2_zfmisc_1(X164,X165))
        | ~ v1_funct_1(X163)
        | v1_relat_1(k5_relat_1(sK3,X163)) )
    | ~ spl9_154 ),
    inference(avatar_component_clause,[],[f2936])).

fof(f13025,plain,
    ( spl9_566
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f13010,f2936,f167,f178,f13023])).

fof(f13023,plain,
    ( spl9_566
  <=> ! [X254,X253,X255] :
        ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,X253)))
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255))
        | ~ v1_funct_1(X253) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_566])])).

fof(f13010,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(sK3)
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,X253)))
        | ~ v1_funct_1(X253)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255)) )
    | ~ spl9_12
    | ~ spl9_154 ),
    inference(resolution,[],[f12861,f168])).

fof(f12905,plain,
    ( ~ spl9_11
    | spl9_564
    | ~ spl9_6
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f12887,f2936,f146,f12903,f157])).

fof(f12903,plain,
    ( spl9_564
  <=> ! [X258,X256,X257] :
        ( ~ v1_funct_1(X256)
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X256,sK4)))
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_564])])).

fof(f12887,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(X256)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258)))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X256,sK4)))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_6
    | ~ spl9_154 ),
    inference(resolution,[],[f12860,f147])).

fof(f12901,plain,
    ( ~ spl9_17
    | spl9_562
    | ~ spl9_12
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f12886,f2936,f167,f12899,f178])).

fof(f12899,plain,
    ( spl9_562
  <=> ! [X254,X253,X255] :
        ( ~ v1_funct_1(X253)
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X253,sK3)))
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_562])])).

fof(f12886,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(X253)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255)))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X253,sK3)))
        | ~ v1_funct_1(sK3) )
    | ~ spl9_12
    | ~ spl9_154 ),
    inference(resolution,[],[f12860,f168])).

fof(f12744,plain,
    ( spl9_560
    | ~ spl9_11
    | ~ spl9_6
    | ~ spl9_122 ),
    inference(avatar_split_clause,[],[f12726,f1168,f146,f157,f12742])).

fof(f12742,plain,
    ( spl9_560
  <=> ! [X258,X256,X257] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,X256)))
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258))
        | ~ v1_funct_1(X256) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_560])])).

fof(f1168,plain,
    ( spl9_122
  <=> ! [X100,X99,X101] :
        ( ~ v1_funct_1(X99)
        | ~ r1_tarski(X99,k2_zfmisc_1(X100,X101))
        | v1_funct_1(k5_relat_1(sK4,X99)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).

fof(f12726,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(sK4)
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,X256)))
        | ~ v1_funct_1(X256)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258)) )
    | ~ spl9_6
    | ~ spl9_122 ),
    inference(resolution,[],[f12577,f147])).

fof(f12577,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3)
        | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_122 ),
    inference(resolution,[],[f12576,f106])).

fof(f12576,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3) )
    | ~ spl9_122 ),
    inference(duplicate_literal_removal,[],[f12573])).

fof(f12573,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_122 ),
    inference(resolution,[],[f12572,f117])).

fof(f12572,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X4,X5)))
        | ~ v1_funct_1(X5) )
    | ~ spl9_122 ),
    inference(duplicate_literal_removal,[],[f12571])).

fof(f12571,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(X4,X5)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_122 ),
    inference(superposition,[],[f3137,f116])).

fof(f3137,plain,
    ( ! [X68,X66,X64,X67,X65,X63] :
        ( v1_funct_1(k5_relat_1(sK4,k1_partfun1(X65,X66,X67,X68,X64,X63)))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))
        | ~ v1_funct_1(X64)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
        | ~ v1_funct_1(k1_partfun1(X65,X66,X67,X68,X64,X63))
        | ~ v1_funct_1(X63) )
    | ~ spl9_122 ),
    inference(resolution,[],[f830,f1169])).

fof(f1169,plain,
    ( ! [X101,X99,X100] :
        ( ~ r1_tarski(X99,k2_zfmisc_1(X100,X101))
        | ~ v1_funct_1(X99)
        | v1_funct_1(k5_relat_1(sK4,X99)) )
    | ~ spl9_122 ),
    inference(avatar_component_clause,[],[f1168])).

fof(f12740,plain,
    ( spl9_558
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_122 ),
    inference(avatar_split_clause,[],[f12725,f1168,f167,f178,f12738])).

fof(f12738,plain,
    ( spl9_558
  <=> ! [X254,X253,X255] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK3,X253)))
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255))
        | ~ v1_funct_1(X253) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_558])])).

fof(f12725,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(sK3)
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK3,X253)))
        | ~ v1_funct_1(X253)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255)) )
    | ~ spl9_12
    | ~ spl9_122 ),
    inference(resolution,[],[f12577,f168])).

fof(f12621,plain,
    ( ~ spl9_11
    | spl9_556
    | ~ spl9_6
    | ~ spl9_122 ),
    inference(avatar_split_clause,[],[f12603,f1168,f146,f12619,f157])).

fof(f12619,plain,
    ( spl9_556
  <=> ! [X258,X256,X257] :
        ( ~ v1_funct_1(X256)
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X256,sK4)))
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_556])])).

fof(f12603,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(X256)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258)))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X256,sK4)))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_6
    | ~ spl9_122 ),
    inference(resolution,[],[f12576,f147])).

fof(f12617,plain,
    ( ~ spl9_17
    | spl9_554
    | ~ spl9_12
    | ~ spl9_122 ),
    inference(avatar_split_clause,[],[f12602,f1168,f167,f12615,f178])).

fof(f12615,plain,
    ( spl9_554
  <=> ! [X254,X253,X255] :
        ( ~ v1_funct_1(X253)
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X253,sK3)))
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_554])])).

fof(f12602,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(X253)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255)))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X253,sK3)))
        | ~ v1_funct_1(sK3) )
    | ~ spl9_12
    | ~ spl9_122 ),
    inference(resolution,[],[f12576,f168])).

fof(f12430,plain,
    ( spl9_552
    | ~ spl9_11
    | ~ spl9_6
    | ~ spl9_120 ),
    inference(avatar_split_clause,[],[f12412,f1164,f146,f157,f12428])).

fof(f12428,plain,
    ( spl9_552
  <=> ! [X258,X256,X257] :
        ( v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK4,X256)))
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258))
        | ~ v1_funct_1(X256) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_552])])).

fof(f1164,plain,
    ( spl9_120
  <=> ! [X96,X98,X97] :
        ( ~ v1_funct_1(X96)
        | ~ r1_tarski(X96,k2_zfmisc_1(X97,X98))
        | v1_funct_1(k5_relat_1(sK3,X96)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).

fof(f12412,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(sK4)
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK4,X256)))
        | ~ v1_funct_1(X256)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258)) )
    | ~ spl9_6
    | ~ spl9_120 ),
    inference(resolution,[],[f12265,f147])).

fof(f12265,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3)
        | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_120 ),
    inference(resolution,[],[f12264,f106])).

fof(f12264,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3) )
    | ~ spl9_120 ),
    inference(duplicate_literal_removal,[],[f12261])).

fof(f12261,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X0,X3)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_120 ),
    inference(resolution,[],[f12260,f117])).

fof(f12260,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X4,X5)))
        | ~ v1_funct_1(X5) )
    | ~ spl9_120 ),
    inference(duplicate_literal_removal,[],[f12259])).

fof(f12259,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k5_relat_1(sK3,k5_relat_1(X4,X5)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_120 ),
    inference(superposition,[],[f3136,f116])).

fof(f3136,plain,
    ( ! [X61,X59,X57,X62,X60,X58] :
        ( v1_funct_1(k5_relat_1(sK3,k1_partfun1(X59,X60,X61,X62,X58,X57)))
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
        | ~ v1_funct_1(X58)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
        | ~ v1_funct_1(k1_partfun1(X59,X60,X61,X62,X58,X57))
        | ~ v1_funct_1(X57) )
    | ~ spl9_120 ),
    inference(resolution,[],[f830,f1165])).

fof(f1165,plain,
    ( ! [X97,X98,X96] :
        ( ~ r1_tarski(X96,k2_zfmisc_1(X97,X98))
        | ~ v1_funct_1(X96)
        | v1_funct_1(k5_relat_1(sK3,X96)) )
    | ~ spl9_120 ),
    inference(avatar_component_clause,[],[f1164])).

fof(f12426,plain,
    ( spl9_550
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_120 ),
    inference(avatar_split_clause,[],[f12411,f1164,f167,f178,f12424])).

fof(f12424,plain,
    ( spl9_550
  <=> ! [X254,X253,X255] :
        ( v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK3,X253)))
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255))
        | ~ v1_funct_1(X253) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_550])])).

fof(f12411,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(sK3)
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK3,X253)))
        | ~ v1_funct_1(X253)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255)) )
    | ~ spl9_12
    | ~ spl9_120 ),
    inference(resolution,[],[f12265,f168])).

fof(f12309,plain,
    ( ~ spl9_11
    | spl9_548
    | ~ spl9_6
    | ~ spl9_120 ),
    inference(avatar_split_clause,[],[f12291,f1164,f146,f12307,f157])).

fof(f12307,plain,
    ( spl9_548
  <=> ! [X258,X256,X257] :
        ( ~ v1_funct_1(X256)
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X256,sK4)))
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_548])])).

fof(f12291,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(X256)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258)))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X256,sK4)))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_6
    | ~ spl9_120 ),
    inference(resolution,[],[f12264,f147])).

fof(f12305,plain,
    ( ~ spl9_17
    | spl9_546
    | ~ spl9_12
    | ~ spl9_120 ),
    inference(avatar_split_clause,[],[f12290,f1164,f167,f12303,f178])).

fof(f12303,plain,
    ( spl9_546
  <=> ! [X254,X253,X255] :
        ( ~ v1_funct_1(X253)
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X253,sK3)))
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_546])])).

fof(f12290,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(X253)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255)))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X253,sK3)))
        | ~ v1_funct_1(sK3) )
    | ~ spl9_12
    | ~ spl9_120 ),
    inference(resolution,[],[f12264,f168])).

fof(f12150,plain,
    ( ~ spl9_11
    | spl9_544
    | ~ spl9_6
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f12132,f2703,f146,f12148,f157])).

fof(f12148,plain,
    ( spl9_544
  <=> ! [X258,X256,X257] :
        ( ~ v1_funct_1(X256)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258))
        | v1_relat_1(k5_relat_1(k5_relat_1(sK4,X256),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_544])])).

fof(f2703,plain,
    ( spl9_144
  <=> ! [X157,X159,X158] :
        ( ~ m1_subset_1(X157,k1_zfmisc_1(k2_zfmisc_1(X158,X159)))
        | v1_relat_1(k5_relat_1(X157,sK4))
        | ~ v1_funct_1(X157) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_144])])).

fof(f12132,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(X256)
        | v1_relat_1(k5_relat_1(k5_relat_1(sK4,X256),sK4))
        | ~ v1_funct_1(sK4)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258)) )
    | ~ spl9_6
    | ~ spl9_144 ),
    inference(resolution,[],[f11985,f147])).

fof(f11985,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | v1_relat_1(k5_relat_1(k5_relat_1(X0,X1),sK4))
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_144 ),
    inference(resolution,[],[f11984,f106])).

fof(f11984,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_relat_1(k5_relat_1(k5_relat_1(X0,X1),sK4))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_144 ),
    inference(duplicate_literal_removal,[],[f11981])).

fof(f11981,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X0,X1),sK4))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_144 ),
    inference(resolution,[],[f11980,f117])).

fof(f11980,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | v1_relat_1(k5_relat_1(k5_relat_1(X4,X5),sK4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_144 ),
    inference(duplicate_literal_removal,[],[f11979])).

fof(f11979,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X4,X5),sK4))
        | ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_144 ),
    inference(superposition,[],[f2803,f116])).

fof(f2803,plain,
    ( ! [X6,X4,X8,X7,X5,X3] :
        ( v1_relat_1(k5_relat_1(k1_partfun1(X3,X4,X5,X6,X7,X8),sK4))
        | ~ v1_funct_1(k1_partfun1(X3,X4,X5,X6,X7,X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_1(X7) )
    | ~ spl9_144 ),
    inference(resolution,[],[f2704,f118])).

fof(f2704,plain,
    ( ! [X158,X159,X157] :
        ( ~ m1_subset_1(X157,k1_zfmisc_1(k2_zfmisc_1(X158,X159)))
        | v1_relat_1(k5_relat_1(X157,sK4))
        | ~ v1_funct_1(X157) )
    | ~ spl9_144 ),
    inference(avatar_component_clause,[],[f2703])).

fof(f12146,plain,
    ( ~ spl9_17
    | spl9_542
    | ~ spl9_12
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f12131,f2703,f167,f12144,f178])).

fof(f12144,plain,
    ( spl9_542
  <=> ! [X254,X253,X255] :
        ( ~ v1_funct_1(X253)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255))
        | v1_relat_1(k5_relat_1(k5_relat_1(sK3,X253),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_542])])).

fof(f12131,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(X253)
        | v1_relat_1(k5_relat_1(k5_relat_1(sK3,X253),sK4))
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255)) )
    | ~ spl9_12
    | ~ spl9_144 ),
    inference(resolution,[],[f11985,f168])).

fof(f12029,plain,
    ( ~ spl9_11
    | spl9_540
    | ~ spl9_6
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f12011,f2703,f146,f12027,f157])).

fof(f12027,plain,
    ( spl9_540
  <=> ! [X258,X256,X257] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X256,sK4),sK4))
        | ~ v1_funct_1(X256)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_540])])).

fof(f12011,plain,
    ( ! [X257,X256,X258] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X256,sK4),sK4))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258)))
        | ~ v1_funct_1(X256) )
    | ~ spl9_6
    | ~ spl9_144 ),
    inference(resolution,[],[f11984,f147])).

fof(f12025,plain,
    ( ~ spl9_17
    | spl9_538
    | ~ spl9_12
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f12010,f2703,f167,f12023,f178])).

fof(f12023,plain,
    ( spl9_538
  <=> ! [X254,X253,X255] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X253,sK3),sK4))
        | ~ v1_funct_1(X253)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_538])])).

fof(f12010,plain,
    ( ! [X255,X253,X254] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X253,sK3),sK4))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255)))
        | ~ v1_funct_1(X253) )
    | ~ spl9_12
    | ~ spl9_144 ),
    inference(resolution,[],[f11984,f168])).

fof(f11873,plain,
    ( ~ spl9_11
    | spl9_536
    | ~ spl9_6
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f11855,f2699,f146,f11871,f157])).

fof(f11871,plain,
    ( spl9_536
  <=> ! [X258,X256,X257] :
        ( ~ v1_funct_1(X256)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258))
        | v1_relat_1(k5_relat_1(k5_relat_1(sK4,X256),sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_536])])).

fof(f2699,plain,
    ( spl9_142
  <=> ! [X155,X154,X156] :
        ( ~ m1_subset_1(X154,k1_zfmisc_1(k2_zfmisc_1(X155,X156)))
        | v1_relat_1(k5_relat_1(X154,sK3))
        | ~ v1_funct_1(X154) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_142])])).

fof(f11855,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(X256)
        | v1_relat_1(k5_relat_1(k5_relat_1(sK4,X256),sK3))
        | ~ v1_funct_1(sK4)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258)) )
    | ~ spl9_6
    | ~ spl9_142 ),
    inference(resolution,[],[f11686,f147])).

fof(f11686,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | v1_relat_1(k5_relat_1(k5_relat_1(X0,X1),sK3))
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_142 ),
    inference(resolution,[],[f11685,f106])).

fof(f11685,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_relat_1(k5_relat_1(k5_relat_1(X0,X1),sK3))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_142 ),
    inference(duplicate_literal_removal,[],[f11682])).

fof(f11682,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X0,X1),sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_142 ),
    inference(resolution,[],[f11681,f117])).

fof(f11681,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | v1_relat_1(k5_relat_1(k5_relat_1(X4,X5),sK3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_142 ),
    inference(duplicate_literal_removal,[],[f11680])).

fof(f11680,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X4,X5),sK3))
        | ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_142 ),
    inference(superposition,[],[f2707,f116])).

fof(f2707,plain,
    ( ! [X6,X4,X8,X7,X5,X3] :
        ( v1_relat_1(k5_relat_1(k1_partfun1(X3,X4,X5,X6,X7,X8),sK3))
        | ~ v1_funct_1(k1_partfun1(X3,X4,X5,X6,X7,X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_1(X7) )
    | ~ spl9_142 ),
    inference(resolution,[],[f2700,f118])).

fof(f2700,plain,
    ( ! [X156,X154,X155] :
        ( ~ m1_subset_1(X154,k1_zfmisc_1(k2_zfmisc_1(X155,X156)))
        | v1_relat_1(k5_relat_1(X154,sK3))
        | ~ v1_funct_1(X154) )
    | ~ spl9_142 ),
    inference(avatar_component_clause,[],[f2699])).

fof(f11869,plain,
    ( ~ spl9_17
    | spl9_534
    | ~ spl9_12
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f11854,f2699,f167,f11867,f178])).

fof(f11867,plain,
    ( spl9_534
  <=> ! [X254,X253,X255] :
        ( ~ v1_funct_1(X253)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255))
        | v1_relat_1(k5_relat_1(k5_relat_1(sK3,X253),sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_534])])).

fof(f11854,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(X253)
        | v1_relat_1(k5_relat_1(k5_relat_1(sK3,X253),sK3))
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255)) )
    | ~ spl9_12
    | ~ spl9_142 ),
    inference(resolution,[],[f11686,f168])).

fof(f11730,plain,
    ( ~ spl9_11
    | spl9_532
    | ~ spl9_6
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f11712,f2699,f146,f11728,f157])).

fof(f11728,plain,
    ( spl9_532
  <=> ! [X258,X256,X257] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X256,sK4),sK3))
        | ~ v1_funct_1(X256)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_532])])).

fof(f11712,plain,
    ( ! [X257,X256,X258] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X256,sK4),sK3))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258)))
        | ~ v1_funct_1(X256) )
    | ~ spl9_6
    | ~ spl9_142 ),
    inference(resolution,[],[f11685,f147])).

fof(f11726,plain,
    ( ~ spl9_17
    | spl9_530
    | ~ spl9_12
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f11711,f2699,f167,f11724,f178])).

fof(f11724,plain,
    ( spl9_530
  <=> ! [X254,X253,X255] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X253,sK3),sK3))
        | ~ v1_funct_1(X253)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_530])])).

fof(f11711,plain,
    ( ! [X255,X253,X254] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(X253,sK3),sK3))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255)))
        | ~ v1_funct_1(X253) )
    | ~ spl9_12
    | ~ spl9_142 ),
    inference(resolution,[],[f11685,f168])).

fof(f11554,plain,
    ( ~ spl9_11
    | spl9_528
    | ~ spl9_6
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f11536,f1008,f146,f11552,f157])).

fof(f11552,plain,
    ( spl9_528
  <=> ! [X258,X256,X257] :
        ( ~ v1_funct_1(X256)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK4,X256),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_528])])).

fof(f1008,plain,
    ( spl9_110
  <=> ! [X100,X99,X101] :
        ( v1_funct_1(k5_relat_1(X99,sK4))
        | ~ v1_funct_1(X99)
        | ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X100,X101))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).

fof(f11536,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(X256)
        | v1_funct_1(k5_relat_1(k5_relat_1(sK4,X256),sK4))
        | ~ v1_funct_1(sK4)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258)) )
    | ~ spl9_6
    | ~ spl9_110 ),
    inference(resolution,[],[f11389,f147])).

fof(f11389,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | v1_funct_1(k5_relat_1(k5_relat_1(X0,X1),sK4))
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_110 ),
    inference(resolution,[],[f11388,f106])).

fof(f11388,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X0,X1),sK4))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_110 ),
    inference(duplicate_literal_removal,[],[f11385])).

fof(f11385,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X0,X1),sK4))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_110 ),
    inference(resolution,[],[f11384,f117])).

fof(f11384,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | v1_funct_1(k5_relat_1(k5_relat_1(X4,X5),sK4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_110 ),
    inference(duplicate_literal_removal,[],[f11383])).

fof(f11383,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X4,X5),sK4))
        | ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_110 ),
    inference(superposition,[],[f1054,f116])).

fof(f1054,plain,
    ( ! [X6,X4,X8,X7,X5,X3] :
        ( v1_funct_1(k5_relat_1(k1_partfun1(X3,X4,X5,X6,X7,X8),sK4))
        | ~ v1_funct_1(k1_partfun1(X3,X4,X5,X6,X7,X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_1(X7) )
    | ~ spl9_110 ),
    inference(resolution,[],[f1009,f118])).

fof(f1009,plain,
    ( ! [X101,X99,X100] :
        ( ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X100,X101)))
        | ~ v1_funct_1(X99)
        | v1_funct_1(k5_relat_1(X99,sK4)) )
    | ~ spl9_110 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f11550,plain,
    ( ~ spl9_17
    | spl9_526
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f11535,f1008,f167,f11548,f178])).

fof(f11548,plain,
    ( spl9_526
  <=> ! [X254,X253,X255] :
        ( ~ v1_funct_1(X253)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK3,X253),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_526])])).

fof(f11535,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(X253)
        | v1_funct_1(k5_relat_1(k5_relat_1(sK3,X253),sK4))
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255)) )
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(resolution,[],[f11389,f168])).

fof(f11433,plain,
    ( ~ spl9_11
    | spl9_524
    | ~ spl9_6
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f11415,f1008,f146,f11431,f157])).

fof(f11431,plain,
    ( spl9_524
  <=> ! [X258,X256,X257] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X256,sK4),sK4))
        | ~ v1_funct_1(X256)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_524])])).

fof(f11415,plain,
    ( ! [X257,X256,X258] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X256,sK4),sK4))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258)))
        | ~ v1_funct_1(X256) )
    | ~ spl9_6
    | ~ spl9_110 ),
    inference(resolution,[],[f11388,f147])).

fof(f11429,plain,
    ( ~ spl9_17
    | spl9_522
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f11414,f1008,f167,f11427,f178])).

fof(f11427,plain,
    ( spl9_522
  <=> ! [X254,X253,X255] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X253,sK3),sK4))
        | ~ v1_funct_1(X253)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_522])])).

fof(f11414,plain,
    ( ! [X255,X253,X254] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X253,sK3),sK4))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255)))
        | ~ v1_funct_1(X253) )
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(resolution,[],[f11388,f168])).

fof(f11257,plain,
    ( ~ spl9_11
    | spl9_520
    | ~ spl9_6
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f11239,f1004,f146,f11255,f157])).

fof(f11255,plain,
    ( spl9_520
  <=> ! [X258,X256,X257] :
        ( ~ v1_funct_1(X256)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK4,X256),sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_520])])).

fof(f1004,plain,
    ( spl9_108
  <=> ! [X96,X98,X97] :
        ( v1_funct_1(k5_relat_1(X96,sK3))
        | ~ v1_funct_1(X96)
        | ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X97,X98))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f11239,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(X256)
        | v1_funct_1(k5_relat_1(k5_relat_1(sK4,X256),sK3))
        | ~ v1_funct_1(sK4)
        | ~ r1_tarski(X256,k2_zfmisc_1(X257,X258)) )
    | ~ spl9_6
    | ~ spl9_108 ),
    inference(resolution,[],[f11092,f147])).

fof(f11092,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | v1_funct_1(k5_relat_1(k5_relat_1(X0,X1),sK3))
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_108 ),
    inference(resolution,[],[f11091,f106])).

fof(f11091,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X0,X1),sK3))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_108 ),
    inference(duplicate_literal_removal,[],[f11088])).

fof(f11088,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X0,X1),sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X0) )
    | ~ spl9_108 ),
    inference(resolution,[],[f11087,f117])).

fof(f11087,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | v1_funct_1(k5_relat_1(k5_relat_1(X4,X5),sK3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_108 ),
    inference(duplicate_literal_removal,[],[f11086])).

fof(f11086,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X4,X5),sK3))
        | ~ v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) )
    | ~ spl9_108 ),
    inference(superposition,[],[f1012,f116])).

fof(f1012,plain,
    ( ! [X6,X4,X8,X7,X5,X3] :
        ( v1_funct_1(k5_relat_1(k1_partfun1(X3,X4,X5,X6,X7,X8),sK3))
        | ~ v1_funct_1(k1_partfun1(X3,X4,X5,X6,X7,X8))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_1(X7) )
    | ~ spl9_108 ),
    inference(resolution,[],[f1005,f118])).

fof(f1005,plain,
    ( ! [X97,X98,X96] :
        ( ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X97,X98)))
        | ~ v1_funct_1(X96)
        | v1_funct_1(k5_relat_1(X96,sK3)) )
    | ~ spl9_108 ),
    inference(avatar_component_clause,[],[f1004])).

fof(f11253,plain,
    ( ~ spl9_17
    | spl9_518
    | ~ spl9_12
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f11238,f1004,f167,f11251,f178])).

fof(f11251,plain,
    ( spl9_518
  <=> ! [X254,X253,X255] :
        ( ~ v1_funct_1(X253)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK3,X253),sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_518])])).

fof(f11238,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(X253)
        | v1_funct_1(k5_relat_1(k5_relat_1(sK3,X253),sK3))
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(X253,k2_zfmisc_1(X254,X255)) )
    | ~ spl9_12
    | ~ spl9_108 ),
    inference(resolution,[],[f11092,f168])).

fof(f11136,plain,
    ( ~ spl9_11
    | spl9_516
    | ~ spl9_6
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f11118,f1004,f146,f11134,f157])).

fof(f11134,plain,
    ( spl9_516
  <=> ! [X258,X256,X257] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X256,sK4),sK3))
        | ~ v1_funct_1(X256)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_516])])).

fof(f11118,plain,
    ( ! [X257,X256,X258] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X256,sK4),sK3))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258)))
        | ~ v1_funct_1(X256) )
    | ~ spl9_6
    | ~ spl9_108 ),
    inference(resolution,[],[f11091,f147])).

fof(f11132,plain,
    ( ~ spl9_17
    | spl9_514
    | ~ spl9_12
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f11117,f1004,f167,f11130,f178])).

fof(f11130,plain,
    ( spl9_514
  <=> ! [X254,X253,X255] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X253,sK3),sK3))
        | ~ v1_funct_1(X253)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_514])])).

fof(f11117,plain,
    ( ! [X255,X253,X254] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X253,sK3),sK3))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255)))
        | ~ v1_funct_1(X253) )
    | ~ spl9_12
    | ~ spl9_108 ),
    inference(resolution,[],[f11091,f168])).

fof(f10740,plain,
    ( spl9_512
    | ~ spl9_11
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f10722,f146,f157,f10738])).

fof(f10738,plain,
    ( spl9_512
  <=> ! [X258,X256,X257] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X256))
        | v1_xboole_0(k5_relat_1(sK4,X257))
        | ~ r1_tarski(X257,k2_zfmisc_1(X258,X256))
        | ~ v1_funct_1(X257) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_512])])).

fof(f10722,plain,
    ( ! [X257,X256,X258] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X256))
        | v1_xboole_0(k5_relat_1(sK4,X257))
        | ~ v1_funct_1(X257)
        | ~ r1_tarski(X257,k2_zfmisc_1(X258,X256)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f10493,f147])).

fof(f10736,plain,
    ( spl9_510
    | ~ spl9_17
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f10721,f167,f178,f10734])).

fof(f10734,plain,
    ( spl9_510
  <=> ! [X254,X253,X255] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X253))
        | v1_xboole_0(k5_relat_1(sK3,X254))
        | ~ r1_tarski(X254,k2_zfmisc_1(X255,X253))
        | ~ v1_funct_1(X254) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_510])])).

fof(f10721,plain,
    ( ! [X255,X253,X254] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X253))
        | v1_xboole_0(k5_relat_1(sK3,X254))
        | ~ v1_funct_1(X254)
        | ~ r1_tarski(X254,k2_zfmisc_1(X255,X253)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f10493,f168])).

fof(f10537,plain,
    ( ~ spl9_11
    | spl9_508
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f10519,f146,f10535,f157])).

fof(f10535,plain,
    ( spl9_508
  <=> ! [X258,X256,X257] :
        ( ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258)))
        | v1_xboole_0(k5_relat_1(X256,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(X257,u1_struct_0(sK1)))
        | ~ v1_funct_1(X256) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_508])])).

fof(f10519,plain,
    ( ! [X257,X256,X258] :
        ( ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,X258)))
        | ~ v1_funct_1(X256)
        | ~ v1_xboole_0(k2_zfmisc_1(X257,u1_struct_0(sK1)))
        | v1_xboole_0(k5_relat_1(X256,sK4))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_6 ),
    inference(resolution,[],[f10492,f147])).

fof(f10533,plain,
    ( ~ spl9_17
    | spl9_506
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f10518,f167,f10531,f178])).

fof(f10531,plain,
    ( spl9_506
  <=> ! [X254,X253,X255] :
        ( ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255)))
        | v1_xboole_0(k5_relat_1(X253,sK3))
        | ~ v1_xboole_0(k2_zfmisc_1(X254,u1_struct_0(sK2)))
        | ~ v1_funct_1(X253) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_506])])).

fof(f10518,plain,
    ( ! [X255,X253,X254] :
        ( ~ m1_subset_1(X253,k1_zfmisc_1(k2_zfmisc_1(X254,X255)))
        | ~ v1_funct_1(X253)
        | ~ v1_xboole_0(k2_zfmisc_1(X254,u1_struct_0(sK2)))
        | v1_xboole_0(k5_relat_1(X253,sK3))
        | ~ v1_funct_1(sK3) )
    | ~ spl9_12 ),
    inference(resolution,[],[f10492,f168])).

fof(f10348,plain,
    ( spl9_356
    | spl9_504
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f10339,f5674,f10346,f5832])).

fof(f5832,plain,
    ( spl9_356
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_356])])).

fof(f10346,plain,
    ( spl9_504
  <=> ! [X879,X878] :
        ( v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))),X878))),X879))
        | ~ v4_pre_topc(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))),X878))),X879)),sK1)
        | v4_pre_topc(k10_relat_1(sK4,sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))),X878))),X879))),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_504])])).

fof(f10339,plain,
    ( ! [X878,X879] :
        ( v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))),X878))),X879))
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))
        | v4_pre_topc(k10_relat_1(sK4,sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))),X878))),X879))),sK2)
        | ~ v4_pre_topc(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))),X878))),X879)),sK1) )
    | ~ spl9_320 ),
    inference(resolution,[],[f1412,f5675])).

fof(f1412,plain,(
    ! [X76,X74,X75] :
      ( m1_subset_1(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(X74)),X75))),X76)),X74)
      | v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(X74)),X75))),X76))
      | v1_xboole_0(sK6(k1_zfmisc_1(X74))) ) ),
    inference(resolution,[],[f883,f373])).

fof(f883,plain,(
    ! [X59,X60,X58] :
      ( r2_hidden(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X58,X59))),X60)),X58)
      | v1_xboole_0(X58)
      | v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X58,X59))),X60)) ) ),
    inference(resolution,[],[f602,f103])).

fof(f602,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2)),X0)
      | v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2)) ) ),
    inference(resolution,[],[f507,f280])).

fof(f507,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X7))
      | m1_subset_1(X4,X5) ) ),
    inference(resolution,[],[f476,f370])).

fof(f10344,plain,
    ( spl9_328
    | spl9_502
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f10338,f5670,f10342,f5723])).

fof(f5723,plain,
    ( spl9_328
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_328])])).

fof(f10342,plain,
    ( spl9_502
  <=> ! [X877,X876] :
        ( v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))),X876))),X877))
        | ~ v4_pre_topc(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))),X876))),X877)),sK2)
        | v4_pre_topc(k10_relat_1(sK3,sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))),X876))),X877))),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_502])])).

fof(f10338,plain,
    ( ! [X876,X877] :
        ( v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))),X876))),X877))
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))
        | v4_pre_topc(k10_relat_1(sK3,sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))),X876))),X877))),sK0)
        | ~ v4_pre_topc(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))),X876))),X877)),sK2) )
    | ~ spl9_318 ),
    inference(resolution,[],[f1412,f5671])).

fof(f9226,plain,
    ( spl9_500
    | ~ spl9_11
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f9210,f146,f157,f9224])).

fof(f9224,plain,
    ( spl9_500
  <=> ! [X242,X244,X241,X243] :
        ( ~ v1_funct_1(X241)
        | ~ r1_tarski(X241,k2_zfmisc_1(X243,X244))
        | m1_subset_1(X242,k2_zfmisc_1(X243,u1_struct_0(sK1)))
        | ~ r2_hidden(X242,k5_relat_1(X241,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_500])])).

fof(f9210,plain,
    ( ! [X243,X241,X244,X242] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_1(X241)
        | m1_subset_1(X242,k2_zfmisc_1(X243,u1_struct_0(sK1)))
        | ~ r2_hidden(X242,k5_relat_1(X241,sK4))
        | ~ r1_tarski(X241,k2_zfmisc_1(X243,X244)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f8565,f147])).

fof(f9222,plain,
    ( spl9_498
    | ~ spl9_17
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f9209,f167,f178,f9220])).

fof(f9220,plain,
    ( spl9_498
  <=> ! [X238,X240,X237,X239] :
        ( ~ v1_funct_1(X237)
        | ~ r1_tarski(X237,k2_zfmisc_1(X239,X240))
        | m1_subset_1(X238,k2_zfmisc_1(X239,u1_struct_0(sK2)))
        | ~ r2_hidden(X238,k5_relat_1(X237,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_498])])).

fof(f9209,plain,
    ( ! [X239,X237,X240,X238] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X237)
        | m1_subset_1(X238,k2_zfmisc_1(X239,u1_struct_0(sK2)))
        | ~ r2_hidden(X238,k5_relat_1(X237,sK3))
        | ~ r1_tarski(X237,k2_zfmisc_1(X239,X240)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f8565,f168])).

fof(f9148,plain,
    ( ~ spl9_23
    | spl9_496
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f9134,f5674,f9146,f199])).

fof(f9146,plain,
    ( spl9_496
  <=> ! [X9,X5,X7,X8,X6] :
        ( v5_pre_topc(k1_partfun1(u1_struct_0(X5),X6,X7,u1_struct_0(sK1),X8,X9),X5,sK1)
        | ~ v4_pre_topc(sK5(X5,sK1,k1_partfun1(u1_struct_0(X5),X6,X7,u1_struct_0(sK1),X8,X9)),sK1)
        | v4_pre_topc(k10_relat_1(sK4,sK5(X5,sK1,k1_partfun1(u1_struct_0(X5),X6,X7,u1_struct_0(sK1),X8,X9))),sK2)
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),X6)))
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,u1_struct_0(sK1))))
        | ~ l1_pre_topc(X5)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X5),X6,X7,u1_struct_0(sK1),X8,X9))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X5),X6,X7,u1_struct_0(sK1),X8,X9),u1_struct_0(X5),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_496])])).

fof(f9134,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( v5_pre_topc(k1_partfun1(u1_struct_0(X5),X6,X7,u1_struct_0(sK1),X8,X9),X5,sK1)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X5),X6,X7,u1_struct_0(sK1),X8,X9),u1_struct_0(X5),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X5),X6,X7,u1_struct_0(sK1),X8,X9))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X5)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,u1_struct_0(sK1))))
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),X6)))
        | ~ v1_funct_1(X8)
        | v4_pre_topc(k10_relat_1(sK4,sK5(X5,sK1,k1_partfun1(u1_struct_0(X5),X6,X7,u1_struct_0(sK1),X8,X9))),sK2)
        | ~ v4_pre_topc(sK5(X5,sK1,k1_partfun1(u1_struct_0(X5),X6,X7,u1_struct_0(sK1),X8,X9)),sK1) )
    | ~ spl9_320 ),
    inference(resolution,[],[f1587,f5675])).

fof(f1587,plain,(
    ! [X6,X4,X8,X7,X5,X3] :
      ( m1_subset_1(sK5(X3,X4,k1_partfun1(u1_struct_0(X3),X5,X6,u1_struct_0(X4),X7,X8)),k1_zfmisc_1(u1_struct_0(X4)))
      | v5_pre_topc(k1_partfun1(u1_struct_0(X3),X5,X6,u1_struct_0(X4),X7,X8),X3,X4)
      | ~ v1_funct_2(k1_partfun1(u1_struct_0(X3),X5,X6,u1_struct_0(X4),X7,X8),u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(k1_partfun1(u1_struct_0(X3),X5,X6,u1_struct_0(X4),X7,X8))
      | ~ l1_pre_topc(X4)
      | ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,u1_struct_0(X4))))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),X5)))
      | ~ v1_funct_1(X7) ) ),
    inference(resolution,[],[f95,f118])).

fof(f9144,plain,
    ( ~ spl9_19
    | spl9_494
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f9133,f5670,f9142,f185])).

fof(f9142,plain,
    ( spl9_494
  <=> ! [X1,X3,X0,X2,X4] :
        ( v5_pre_topc(k1_partfun1(u1_struct_0(X0),X1,X2,u1_struct_0(sK2),X3,X4),X0,sK2)
        | ~ v4_pre_topc(sK5(X0,sK2,k1_partfun1(u1_struct_0(X0),X1,X2,u1_struct_0(sK2),X3,X4)),sK2)
        | v4_pre_topc(k10_relat_1(sK3,sK5(X0,sK2,k1_partfun1(u1_struct_0(X0),X1,X2,u1_struct_0(sK2),X3,X4))),sK0)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK2))))
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),X1,X2,u1_struct_0(sK2),X3,X4))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),X1,X2,u1_struct_0(sK2),X3,X4),u1_struct_0(X0),u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_494])])).

fof(f9133,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v5_pre_topc(k1_partfun1(u1_struct_0(X0),X1,X2,u1_struct_0(sK2),X3,X4),X0,sK2)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),X1,X2,u1_struct_0(sK2),X3,X4),u1_struct_0(X0),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),X1,X2,u1_struct_0(sK2),X3,X4))
        | ~ l1_pre_topc(sK2)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(sK2))))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X1)))
        | ~ v1_funct_1(X3)
        | v4_pre_topc(k10_relat_1(sK3,sK5(X0,sK2,k1_partfun1(u1_struct_0(X0),X1,X2,u1_struct_0(sK2),X3,X4))),sK0)
        | ~ v4_pre_topc(sK5(X0,sK2,k1_partfun1(u1_struct_0(X0),X1,X2,u1_struct_0(sK2),X3,X4)),sK2) )
    | ~ spl9_318 ),
    inference(resolution,[],[f1587,f5671])).

fof(f8987,plain,
    ( ~ spl9_493
    | ~ spl9_462 ),
    inference(avatar_split_clause,[],[f8980,f8842,f8985])).

fof(f8985,plain,
    ( spl9_493
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k5_relat_1(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_493])])).

fof(f8842,plain,
    ( spl9_462
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k5_relat_1(sK4,sK4))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_462])])).

fof(f8980,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k5_relat_1(sK4,sK4))
    | ~ spl9_462 ),
    inference(duplicate_literal_removal,[],[f8976])).

fof(f8976,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k5_relat_1(sK4,sK4))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k5_relat_1(sK4,sK4))
    | ~ spl9_462 ),
    inference(resolution,[],[f8944,f8843])).

fof(f8843,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | ~ r2_hidden(X0,k5_relat_1(sK4,sK4)) )
    | ~ spl9_462 ),
    inference(avatar_component_clause,[],[f8842])).

fof(f8944,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),X1)
        | ~ r2_hidden(X1,k5_relat_1(sK4,sK4)) )
    | ~ spl9_462 ),
    inference(resolution,[],[f8843,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',antisymmetry_r2_hidden)).

fof(f8972,plain,
    ( ~ spl9_491
    | ~ spl9_460 ),
    inference(avatar_split_clause,[],[f8965,f8837,f8970])).

fof(f8970,plain,
    ( spl9_491
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),k5_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_491])])).

fof(f8837,plain,
    ( spl9_460
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k5_relat_1(sK4,sK3))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_460])])).

fof(f8965,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),k5_relat_1(sK4,sK3))
    | ~ spl9_460 ),
    inference(duplicate_literal_removal,[],[f8963])).

fof(f8963,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),k5_relat_1(sK4,sK3))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),k5_relat_1(sK4,sK3))
    | ~ spl9_460 ),
    inference(resolution,[],[f8888,f8838])).

fof(f8838,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
        | ~ r2_hidden(X0,k5_relat_1(sK4,sK3)) )
    | ~ spl9_460 ),
    inference(avatar_component_clause,[],[f8837])).

fof(f8888,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),X1)
        | ~ r2_hidden(X1,k5_relat_1(sK4,sK3)) )
    | ~ spl9_460 ),
    inference(resolution,[],[f8838,f101])).

fof(f8957,plain,
    ( ~ spl9_441
    | ~ spl9_489
    | ~ spl9_418
    | ~ spl9_462 ),
    inference(avatar_split_clause,[],[f8946,f8842,f8647,f8955,f8726])).

fof(f8726,plain,
    ( spl9_441
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_441])])).

fof(f8955,plain,
    ( spl9_489
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_489])])).

fof(f8647,plain,
    ( spl9_418
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k5_relat_1(sK3,sK3))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_418])])).

fof(f8946,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK4,sK4))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k5_relat_1(sK3,sK3))
    | ~ spl9_418
    | ~ spl9_462 ),
    inference(resolution,[],[f8843,f8717])).

fof(f8717,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),X1)
        | ~ r2_hidden(X1,k5_relat_1(sK3,sK3)) )
    | ~ spl9_418 ),
    inference(resolution,[],[f8648,f101])).

fof(f8648,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ r2_hidden(X0,k5_relat_1(sK3,sK3)) )
    | ~ spl9_418 ),
    inference(avatar_component_clause,[],[f8647])).

fof(f8940,plain,
    ( ~ spl9_485
    | ~ spl9_487
    | ~ spl9_68
    | ~ spl9_460 ),
    inference(avatar_split_clause,[],[f8893,f8837,f391,f8938,f8932])).

fof(f8932,plain,
    ( spl9_485
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_485])])).

fof(f8938,plain,
    ( spl9_487
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k5_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_487])])).

fof(f391,plain,
    ( spl9_68
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f8893,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k5_relat_1(sK4,sK3))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK4)
    | ~ spl9_68
    | ~ spl9_460 ),
    inference(resolution,[],[f8838,f8875])).

fof(f8875,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),X1)
        | ~ r2_hidden(X1,sK4) )
    | ~ spl9_68 ),
    inference(resolution,[],[f392,f101])).

fof(f392,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | ~ r2_hidden(X0,sK4) )
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f391])).

fof(f8927,plain,
    ( ~ spl9_481
    | ~ spl9_483
    | ~ spl9_430
    | ~ spl9_460 ),
    inference(avatar_split_clause,[],[f8892,f8837,f8689,f8925,f8919])).

fof(f8919,plain,
    ( spl9_481
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_481])])).

fof(f8925,plain,
    ( spl9_483
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k5_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_483])])).

fof(f8689,plain,
    ( spl9_430
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k5_relat_1(sK3,sK4))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_430])])).

fof(f8892,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k5_relat_1(sK4,sK3))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),k5_relat_1(sK3,sK4))
    | ~ spl9_430
    | ~ spl9_460 ),
    inference(resolution,[],[f8838,f8730])).

fof(f8730,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),X1)
        | ~ r2_hidden(X1,k5_relat_1(sK3,sK4)) )
    | ~ spl9_430 ),
    inference(resolution,[],[f8690,f101])).

fof(f8690,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ r2_hidden(X0,k5_relat_1(sK3,sK4)) )
    | ~ spl9_430 ),
    inference(avatar_component_clause,[],[f8689])).

fof(f8914,plain,
    ( ~ spl9_479
    | ~ spl9_477
    | ~ spl9_64
    | ~ spl9_460 ),
    inference(avatar_split_clause,[],[f8891,f8837,f377,f8905,f8912])).

fof(f8912,plain,
    ( spl9_479
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_479])])).

fof(f8905,plain,
    ( spl9_477
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_477])])).

fof(f377,plain,
    ( spl9_64
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f8891,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK4,sK3))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK3)
    | ~ spl9_64
    | ~ spl9_460 ),
    inference(resolution,[],[f8838,f8679])).

fof(f8679,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),X1)
        | ~ r2_hidden(X1,sK3) )
    | ~ spl9_64 ),
    inference(resolution,[],[f378,f101])).

fof(f378,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f377])).

fof(f8907,plain,
    ( ~ spl9_475
    | ~ spl9_477
    | ~ spl9_418
    | ~ spl9_460 ),
    inference(avatar_split_clause,[],[f8890,f8837,f8647,f8905,f8899])).

fof(f8899,plain,
    ( spl9_475
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_475])])).

fof(f8890,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK4,sK3))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)),k5_relat_1(sK3,sK3))
    | ~ spl9_418
    | ~ spl9_460 ),
    inference(resolution,[],[f8838,f8717])).

fof(f8873,plain,
    ( ~ spl9_63
    | spl9_60
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f368,f266,f357,f363])).

fof(f363,plain,
    ( spl9_63
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).

fof(f357,plain,
    ( spl9_60
  <=> ! [X4] : ~ r2_hidden(X4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f266,plain,
    ( spl9_38
  <=> r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f368,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK4)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) )
    | ~ spl9_38 ),
    inference(resolution,[],[f342,f267])).

fof(f267,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f266])).

fof(f342,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f111,f106])).

fof(f8872,plain,
    ( ~ spl9_11
    | ~ spl9_63
    | spl9_472
    | ~ spl9_6
    | ~ spl9_308 ),
    inference(avatar_split_clause,[],[f5509,f5431,f146,f8868,f363,f157])).

fof(f8868,plain,
    ( spl9_472
  <=> ! [X82] : ~ r2_hidden(X82,k5_relat_1(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_472])])).

fof(f5431,plain,
    ( spl9_308
  <=> ! [X197,X199,X196,X198] :
        ( ~ v1_funct_1(X196)
        | ~ r2_hidden(X199,k5_relat_1(sK4,X196))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X198))
        | ~ m1_subset_1(X196,k1_zfmisc_1(k2_zfmisc_1(X197,X198))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_308])])).

fof(f5509,plain,
    ( ! [X139] :
        ( ~ r2_hidden(X139,k5_relat_1(sK4,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_6
    | ~ spl9_308 ),
    inference(resolution,[],[f5432,f147])).

fof(f5432,plain,
    ( ! [X198,X196,X199,X197] :
        ( ~ m1_subset_1(X196,k1_zfmisc_1(k2_zfmisc_1(X197,X198)))
        | ~ r2_hidden(X199,k5_relat_1(sK4,X196))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X198))
        | ~ v1_funct_1(X196) )
    | ~ spl9_308 ),
    inference(avatar_component_clause,[],[f5431])).

fof(f8871,plain,
    ( spl9_472
    | ~ spl9_11
    | ~ spl9_63
    | ~ spl9_38
    | ~ spl9_308 ),
    inference(avatar_split_clause,[],[f5539,f5431,f266,f363,f157,f8868])).

fof(f5539,plain,
    ( ! [X82] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | ~ v1_funct_1(sK4)
        | ~ r2_hidden(X82,k5_relat_1(sK4,sK4)) )
    | ~ spl9_38
    | ~ spl9_308 ),
    inference(resolution,[],[f5490,f267])).

fof(f5490,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X1,k2_zfmisc_1(X3,X2))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X2))
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X0,k5_relat_1(sK4,X1)) )
    | ~ spl9_308 ),
    inference(resolution,[],[f5432,f106])).

fof(f8870,plain,
    ( ~ spl9_63
    | spl9_472
    | ~ spl9_11
    | ~ spl9_38
    | ~ spl9_384 ),
    inference(avatar_split_clause,[],[f6083,f6049,f266,f157,f8868,f363])).

fof(f6049,plain,
    ( spl9_384
  <=> ! [X197,X199,X196,X198] :
        ( ~ v1_funct_1(X196)
        | ~ r1_tarski(X196,k2_zfmisc_1(X197,X199))
        | ~ r2_hidden(X198,k5_relat_1(X196,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(X197,u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_384])])).

fof(f6083,plain,
    ( ! [X82] :
        ( ~ v1_funct_1(sK4)
        | ~ r2_hidden(X82,k5_relat_1(sK4,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) )
    | ~ spl9_38
    | ~ spl9_384 ),
    inference(resolution,[],[f6050,f267])).

fof(f6050,plain,
    ( ! [X198,X196,X199,X197] :
        ( ~ r1_tarski(X196,k2_zfmisc_1(X197,X199))
        | ~ v1_funct_1(X196)
        | ~ r2_hidden(X198,k5_relat_1(X196,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(X197,u1_struct_0(sK1))) )
    | ~ spl9_384 ),
    inference(avatar_component_clause,[],[f6049])).

fof(f8866,plain,
    ( ~ spl9_11
    | ~ spl9_63
    | spl9_470
    | ~ spl9_6
    | ~ spl9_308 ),
    inference(avatar_split_clause,[],[f7610,f5431,f146,f8864,f363,f157])).

fof(f8864,plain,
    ( spl9_470
  <=> ! [X219,X220,X218] :
        ( ~ v1_funct_1(k5_relat_1(X218,sK4))
        | v1_xboole_0(k5_relat_1(sK4,k5_relat_1(X218,sK4)))
        | ~ v1_funct_1(X218)
        | ~ m1_subset_1(X218,k1_zfmisc_1(k2_zfmisc_1(X219,X220))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_470])])).

fof(f7610,plain,
    ( ! [X218,X220,X219] :
        ( ~ v1_funct_1(k5_relat_1(X218,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X218,k1_zfmisc_1(k2_zfmisc_1(X219,X220)))
        | ~ v1_funct_1(X218)
        | v1_xboole_0(k5_relat_1(sK4,k5_relat_1(X218,sK4))) )
    | ~ spl9_6
    | ~ spl9_308 ),
    inference(resolution,[],[f7580,f147])).

fof(f7580,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
        | ~ v1_funct_1(k5_relat_1(X1,X2))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X1)
        | v1_xboole_0(k5_relat_1(sK4,k5_relat_1(X1,X2))) )
    | ~ spl9_308 ),
    inference(resolution,[],[f5493,f280])).

fof(f5493,plain,
    ( ! [X23,X21,X19,X17,X22,X20,X18] :
        ( ~ r2_hidden(X17,k5_relat_1(sK4,k5_relat_1(X18,X19)))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X20))
        | ~ v1_funct_1(k5_relat_1(X18,X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X21,X20)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ v1_funct_1(X18) )
    | ~ spl9_308 ),
    inference(resolution,[],[f5432,f833])).

fof(f8862,plain,
    ( ~ spl9_63
    | ~ spl9_11
    | ~ spl9_115
    | spl9_468
    | ~ spl9_6
    | ~ spl9_402 ),
    inference(avatar_split_clause,[],[f8288,f8258,f146,f8860,f1037,f157,f363])).

fof(f1037,plain,
    ( spl9_115
  <=> ~ v1_funct_1(k5_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_115])])).

fof(f8860,plain,
    ( spl9_468
  <=> v1_xboole_0(k5_relat_1(k5_relat_1(sK4,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_468])])).

fof(f8258,plain,
    ( spl9_402
  <=> ! [X217,X215,X216] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X215,u1_struct_0(sK1)))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X216,sK3),sK4))
        | ~ v1_funct_1(k5_relat_1(X216,sK3))
        | ~ v1_funct_1(X216)
        | ~ m1_subset_1(X216,k1_zfmisc_1(k2_zfmisc_1(X215,X217))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_402])])).

fof(f8288,plain,
    ( v1_xboole_0(k5_relat_1(k5_relat_1(sK4,sK3),sK4))
    | ~ v1_funct_1(k5_relat_1(sK4,sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ spl9_6
    | ~ spl9_402 ),
    inference(resolution,[],[f8259,f147])).

fof(f8259,plain,
    ( ! [X216,X215,X217] :
        ( ~ m1_subset_1(X216,k1_zfmisc_1(k2_zfmisc_1(X215,X217)))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X216,sK3),sK4))
        | ~ v1_funct_1(k5_relat_1(X216,sK3))
        | ~ v1_funct_1(X216)
        | ~ v1_xboole_0(k2_zfmisc_1(X215,u1_struct_0(sK1))) )
    | ~ spl9_402 ),
    inference(avatar_component_clause,[],[f8258])).

fof(f8855,plain,
    ( ~ spl9_63
    | ~ spl9_11
    | ~ spl9_119
    | spl9_466
    | ~ spl9_6
    | ~ spl9_404 ),
    inference(avatar_split_clause,[],[f8320,f8262,f146,f8853,f1079,f157,f363])).

fof(f1079,plain,
    ( spl9_119
  <=> ~ v1_funct_1(k5_relat_1(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).

fof(f8853,plain,
    ( spl9_466
  <=> v1_xboole_0(k5_relat_1(k5_relat_1(sK4,sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_466])])).

fof(f8262,plain,
    ( spl9_404
  <=> ! [X219,X220,X218] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X218,u1_struct_0(sK1)))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X219,sK4),sK4))
        | ~ v1_funct_1(k5_relat_1(X219,sK4))
        | ~ v1_funct_1(X219)
        | ~ m1_subset_1(X219,k1_zfmisc_1(k2_zfmisc_1(X218,X220))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_404])])).

fof(f8320,plain,
    ( v1_xboole_0(k5_relat_1(k5_relat_1(sK4,sK4),sK4))
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ spl9_6
    | ~ spl9_404 ),
    inference(resolution,[],[f8263,f147])).

fof(f8263,plain,
    ( ! [X218,X220,X219] :
        ( ~ m1_subset_1(X219,k1_zfmisc_1(k2_zfmisc_1(X218,X220)))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X219,sK4),sK4))
        | ~ v1_funct_1(k5_relat_1(X219,sK4))
        | ~ v1_funct_1(X219)
        | ~ v1_xboole_0(k2_zfmisc_1(X218,u1_struct_0(sK1))) )
    | ~ spl9_404 ),
    inference(avatar_component_clause,[],[f8262])).

fof(f8848,plain,
    ( ~ spl9_11
    | ~ spl9_63
    | spl9_464
    | ~ spl9_6
    | ~ spl9_384 ),
    inference(avatar_split_clause,[],[f8352,f6049,f146,f8846,f363,f157])).

fof(f8846,plain,
    ( spl9_464
  <=> ! [X219,X220,X218] :
        ( ~ v1_funct_1(X218)
        | ~ r1_tarski(X218,k2_zfmisc_1(X219,X220))
        | v1_xboole_0(k5_relat_1(k5_relat_1(sK4,X218),sK4))
        | ~ v1_funct_1(k5_relat_1(sK4,X218)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_464])])).

fof(f8352,plain,
    ( ! [X218,X220,X219] :
        ( ~ v1_funct_1(X218)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k5_relat_1(sK4,X218))
        | v1_xboole_0(k5_relat_1(k5_relat_1(sK4,X218),sK4))
        | ~ r1_tarski(X218,k2_zfmisc_1(X219,X220)) )
    | ~ spl9_6
    | ~ spl9_384 ),
    inference(resolution,[],[f8225,f147])).

fof(f8225,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ v1_funct_1(X1)
        | ~ v1_xboole_0(k2_zfmisc_1(X0,u1_struct_0(sK1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(k5_relat_1(X2,X1))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X2,X1),sK4))
        | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_384 ),
    inference(resolution,[],[f8218,f106])).

fof(f8218,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_xboole_0(k2_zfmisc_1(X2,u1_struct_0(sK1)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(X0,X1))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X0,X1),sK4)) )
    | ~ spl9_384 ),
    inference(resolution,[],[f6073,f280])).

fof(f6073,plain,
    ( ! [X14,X19,X17,X15,X13,X18,X16] :
        ( ~ r2_hidden(X15,k5_relat_1(k5_relat_1(X13,X14),sK4))
        | ~ v1_funct_1(k5_relat_1(X13,X14))
        | ~ v1_xboole_0(k2_zfmisc_1(X16,u1_struct_0(sK1)))
        | ~ v1_funct_1(X14)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
    | ~ spl9_384 ),
    inference(resolution,[],[f6050,f2800])).

fof(f8844,plain,
    ( spl9_62
    | spl9_462
    | ~ spl9_458 ),
    inference(avatar_split_clause,[],[f8840,f8832,f8842,f360])).

fof(f360,plain,
    ( spl9_62
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f8832,plain,
    ( spl9_458
  <=> ! [X172] :
        ( ~ r2_hidden(X172,k5_relat_1(sK4,sK4))
        | m1_subset_1(X172,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_458])])).

fof(f8840,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_relat_1(sK4,sK4))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) )
    | ~ spl9_458 ),
    inference(resolution,[],[f8833,f103])).

fof(f8833,plain,
    ( ! [X172] :
        ( m1_subset_1(X172,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | ~ r2_hidden(X172,k5_relat_1(sK4,sK4)) )
    | ~ spl9_458 ),
    inference(avatar_component_clause,[],[f8832])).

fof(f8839,plain,
    ( spl9_314
    | spl9_460
    | ~ spl9_456 ),
    inference(avatar_split_clause,[],[f8835,f8828,f8837,f5518])).

fof(f5518,plain,
    ( spl9_314
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_314])])).

fof(f8828,plain,
    ( spl9_456
  <=> ! [X171] :
        ( ~ r2_hidden(X171,k5_relat_1(sK4,sK3))
        | m1_subset_1(X171,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_456])])).

fof(f8835,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_relat_1(sK4,sK3))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) )
    | ~ spl9_456 ),
    inference(resolution,[],[f8829,f103])).

fof(f8829,plain,
    ( ! [X171] :
        ( m1_subset_1(X171,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
        | ~ r2_hidden(X171,k5_relat_1(sK4,sK3)) )
    | ~ spl9_456 ),
    inference(avatar_component_clause,[],[f8828])).

fof(f8834,plain,
    ( ~ spl9_11
    | spl9_458
    | ~ spl9_6
    | ~ spl9_412 ),
    inference(avatar_split_clause,[],[f8818,f8602,f146,f8832,f157])).

fof(f8602,plain,
    ( spl9_412
  <=> ! [X242,X244,X241,X243] :
        ( ~ v1_funct_1(X241)
        | ~ r2_hidden(X244,k5_relat_1(sK4,X241))
        | m1_subset_1(X244,k2_zfmisc_1(u1_struct_0(sK2),X243))
        | ~ m1_subset_1(X241,k1_zfmisc_1(k2_zfmisc_1(X242,X243))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_412])])).

fof(f8818,plain,
    ( ! [X172] :
        ( ~ r2_hidden(X172,k5_relat_1(sK4,sK4))
        | m1_subset_1(X172,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_6
    | ~ spl9_412 ),
    inference(resolution,[],[f8603,f147])).

fof(f8603,plain,
    ( ! [X243,X241,X244,X242] :
        ( ~ m1_subset_1(X241,k1_zfmisc_1(k2_zfmisc_1(X242,X243)))
        | ~ r2_hidden(X244,k5_relat_1(sK4,X241))
        | m1_subset_1(X244,k2_zfmisc_1(u1_struct_0(sK2),X243))
        | ~ v1_funct_1(X241) )
    | ~ spl9_412 ),
    inference(avatar_component_clause,[],[f8602])).

fof(f8830,plain,
    ( ~ spl9_17
    | spl9_456
    | ~ spl9_12
    | ~ spl9_412 ),
    inference(avatar_split_clause,[],[f8817,f8602,f167,f8828,f178])).

fof(f8817,plain,
    ( ! [X171] :
        ( ~ r2_hidden(X171,k5_relat_1(sK4,sK3))
        | m1_subset_1(X171,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
        | ~ v1_funct_1(sK3) )
    | ~ spl9_12
    | ~ spl9_412 ),
    inference(resolution,[],[f8603,f168])).

fof(f8793,plain,
    ( ~ spl9_455
    | ~ spl9_430 ),
    inference(avatar_split_clause,[],[f8786,f8689,f8791])).

fof(f8791,plain,
    ( spl9_455
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_455])])).

fof(f8786,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k5_relat_1(sK3,sK4))
    | ~ spl9_430 ),
    inference(duplicate_literal_removal,[],[f8784])).

fof(f8784,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k5_relat_1(sK3,sK4))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k5_relat_1(sK3,sK4))
    | ~ spl9_430 ),
    inference(resolution,[],[f8730,f8690])).

fof(f8780,plain,
    ( ~ spl9_445
    | ~ spl9_453
    | ~ spl9_418
    | ~ spl9_430 ),
    inference(avatar_split_clause,[],[f8764,f8689,f8647,f8778,f8745])).

fof(f8745,plain,
    ( spl9_445
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_445])])).

fof(f8778,plain,
    ( spl9_453
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_453])])).

fof(f8764,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k5_relat_1(sK3,sK3))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK3,sK4))
    | ~ spl9_418
    | ~ spl9_430 ),
    inference(resolution,[],[f8717,f8690])).

fof(f8773,plain,
    ( ~ spl9_451
    | ~ spl9_418 ),
    inference(avatar_split_clause,[],[f8766,f8647,f8771])).

fof(f8771,plain,
    ( spl9_451
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_451])])).

fof(f8766,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK3,sK3))
    | ~ spl9_418 ),
    inference(duplicate_literal_removal,[],[f8762])).

fof(f8762,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK3,sK3))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK3,sK3))
    | ~ spl9_418 ),
    inference(resolution,[],[f8717,f8648])).

fof(f8760,plain,
    ( ~ spl9_447
    | ~ spl9_449
    | ~ spl9_68
    | ~ spl9_430 ),
    inference(avatar_split_clause,[],[f8733,f8689,f391,f8758,f8752])).

fof(f8752,plain,
    ( spl9_447
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_447])])).

fof(f8758,plain,
    ( spl9_449
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_449])])).

fof(f8733,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k5_relat_1(sK3,sK4))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK4)
    | ~ spl9_68
    | ~ spl9_430 ),
    inference(resolution,[],[f8690,f398])).

fof(f398,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),X1)
        | ~ r2_hidden(X1,sK4) )
    | ~ spl9_68 ),
    inference(resolution,[],[f392,f101])).

fof(f8747,plain,
    ( ~ spl9_443
    | ~ spl9_445
    | ~ spl9_64
    | ~ spl9_430 ),
    inference(avatar_split_clause,[],[f8732,f8689,f377,f8745,f8739])).

fof(f8739,plain,
    ( spl9_443
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_443])])).

fof(f8732,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),k5_relat_1(sK3,sK4))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK3)
    | ~ spl9_64
    | ~ spl9_430 ),
    inference(resolution,[],[f8690,f8679])).

fof(f8728,plain,
    ( ~ spl9_73
    | ~ spl9_441
    | ~ spl9_68
    | ~ spl9_418 ),
    inference(avatar_split_clause,[],[f8720,f8647,f391,f8726,f414])).

fof(f414,plain,
    ( spl9_73
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).

fof(f8720,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),k5_relat_1(sK3,sK3))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),sK4)
    | ~ spl9_68
    | ~ spl9_418 ),
    inference(resolution,[],[f8648,f398])).

fof(f8715,plain,
    ( spl9_312
    | ~ spl9_11
    | ~ spl9_311
    | ~ spl9_38
    | ~ spl9_306 ),
    inference(avatar_split_clause,[],[f5483,f5427,f266,f5465,f157,f5468])).

fof(f5468,plain,
    ( spl9_312
  <=> ! [X139] : ~ r2_hidden(X139,k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_312])])).

fof(f5465,plain,
    ( spl9_311
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_311])])).

fof(f5427,plain,
    ( spl9_306
  <=> ! [X193,X195,X192,X194] :
        ( ~ v1_funct_1(X192)
        | ~ r2_hidden(X195,k5_relat_1(sK3,X192))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X194))
        | ~ m1_subset_1(X192,k1_zfmisc_1(k2_zfmisc_1(X193,X194))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_306])])).

fof(f5483,plain,
    ( ! [X82] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ v1_funct_1(sK4)
        | ~ r2_hidden(X82,k5_relat_1(sK3,sK4)) )
    | ~ spl9_38
    | ~ spl9_306 ),
    inference(resolution,[],[f5434,f267])).

fof(f5434,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X1,k2_zfmisc_1(X3,X2))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X2))
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X0,k5_relat_1(sK3,X1)) )
    | ~ spl9_306 ),
    inference(resolution,[],[f5428,f106])).

fof(f5428,plain,
    ( ! [X194,X192,X195,X193] :
        ( ~ m1_subset_1(X192,k1_zfmisc_1(k2_zfmisc_1(X193,X194)))
        | ~ r2_hidden(X195,k5_relat_1(sK3,X192))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X194))
        | ~ v1_funct_1(X192) )
    | ~ spl9_306 ),
    inference(avatar_component_clause,[],[f5427])).

fof(f8714,plain,
    ( ~ spl9_311
    | spl9_312
    | ~ spl9_17
    | ~ spl9_40
    | ~ spl9_384 ),
    inference(avatar_split_clause,[],[f6082,f6049,f273,f178,f5468,f5465])).

fof(f273,plain,
    ( spl9_40
  <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f6082,plain,
    ( ! [X81] :
        ( ~ v1_funct_1(sK3)
        | ~ r2_hidden(X81,k5_relat_1(sK3,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) )
    | ~ spl9_40
    | ~ spl9_384 ),
    inference(resolution,[],[f6050,f274])).

fof(f274,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f273])).

fof(f8713,plain,
    ( ~ spl9_11
    | ~ spl9_311
    | spl9_438
    | ~ spl9_6
    | ~ spl9_306 ),
    inference(avatar_split_clause,[],[f7405,f5427,f146,f8711,f5465,f157])).

fof(f8711,plain,
    ( spl9_438
  <=> ! [X219,X220,X218] :
        ( ~ v1_funct_1(k5_relat_1(X218,sK4))
        | v1_xboole_0(k5_relat_1(sK3,k5_relat_1(X218,sK4)))
        | ~ v1_funct_1(X218)
        | ~ m1_subset_1(X218,k1_zfmisc_1(k2_zfmisc_1(X219,X220))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_438])])).

fof(f7405,plain,
    ( ! [X218,X220,X219] :
        ( ~ v1_funct_1(k5_relat_1(X218,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X218,k1_zfmisc_1(k2_zfmisc_1(X219,X220)))
        | ~ v1_funct_1(X218)
        | v1_xboole_0(k5_relat_1(sK3,k5_relat_1(X218,sK4))) )
    | ~ spl9_6
    | ~ spl9_306 ),
    inference(resolution,[],[f7375,f147])).

fof(f7375,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
        | ~ v1_funct_1(k5_relat_1(X1,X2))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X1)
        | v1_xboole_0(k5_relat_1(sK3,k5_relat_1(X1,X2))) )
    | ~ spl9_306 ),
    inference(resolution,[],[f5437,f280])).

fof(f5437,plain,
    ( ! [X23,X21,X19,X17,X22,X20,X18] :
        ( ~ r2_hidden(X17,k5_relat_1(sK3,k5_relat_1(X18,X19)))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X20))
        | ~ v1_funct_1(k5_relat_1(X18,X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X21,X20)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ v1_funct_1(X18) )
    | ~ spl9_306 ),
    inference(resolution,[],[f5428,f833])).

fof(f8709,plain,
    ( ~ spl9_311
    | ~ spl9_17
    | ~ spl9_113
    | spl9_436
    | ~ spl9_12
    | ~ spl9_402 ),
    inference(avatar_split_clause,[],[f8287,f8258,f167,f8707,f1030,f178,f5465])).

fof(f1030,plain,
    ( spl9_113
  <=> ~ v1_funct_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_113])])).

fof(f8707,plain,
    ( spl9_436
  <=> v1_xboole_0(k5_relat_1(k5_relat_1(sK3,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_436])])).

fof(f8287,plain,
    ( v1_xboole_0(k5_relat_1(k5_relat_1(sK3,sK3),sK4))
    | ~ v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl9_12
    | ~ spl9_402 ),
    inference(resolution,[],[f8259,f168])).

fof(f8702,plain,
    ( ~ spl9_311
    | ~ spl9_17
    | ~ spl9_117
    | spl9_434
    | ~ spl9_12
    | ~ spl9_404 ),
    inference(avatar_split_clause,[],[f8319,f8262,f167,f8700,f1072,f178,f5465])).

fof(f8700,plain,
    ( spl9_434
  <=> v1_xboole_0(k5_relat_1(k5_relat_1(sK3,sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_434])])).

fof(f8319,plain,
    ( v1_xboole_0(k5_relat_1(k5_relat_1(sK3,sK4),sK4))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK3)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl9_12
    | ~ spl9_404 ),
    inference(resolution,[],[f8263,f168])).

fof(f8695,plain,
    ( ~ spl9_17
    | ~ spl9_311
    | spl9_432
    | ~ spl9_12
    | ~ spl9_384 ),
    inference(avatar_split_clause,[],[f8351,f6049,f167,f8693,f5465,f178])).

fof(f8693,plain,
    ( spl9_432
  <=> ! [X217,X215,X216] :
        ( ~ v1_funct_1(X215)
        | ~ r1_tarski(X215,k2_zfmisc_1(X216,X217))
        | v1_xboole_0(k5_relat_1(k5_relat_1(sK3,X215),sK4))
        | ~ v1_funct_1(k5_relat_1(sK3,X215)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_432])])).

fof(f8351,plain,
    ( ! [X216,X215,X217] :
        ( ~ v1_funct_1(X215)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(k5_relat_1(sK3,X215))
        | v1_xboole_0(k5_relat_1(k5_relat_1(sK3,X215),sK4))
        | ~ r1_tarski(X215,k2_zfmisc_1(X216,X217)) )
    | ~ spl9_12
    | ~ spl9_384 ),
    inference(resolution,[],[f8225,f168])).

fof(f8691,plain,
    ( spl9_310
    | spl9_430
    | ~ spl9_416 ),
    inference(avatar_split_clause,[],[f8687,f8642,f8689,f5462])).

fof(f5462,plain,
    ( spl9_310
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_310])])).

fof(f8642,plain,
    ( spl9_416
  <=> ! [X172] :
        ( ~ r2_hidden(X172,k5_relat_1(sK3,sK4))
        | m1_subset_1(X172,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_416])])).

fof(f8687,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_relat_1(sK3,sK4))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) )
    | ~ spl9_416 ),
    inference(resolution,[],[f8643,f103])).

fof(f8643,plain,
    ( ! [X172] :
        ( m1_subset_1(X172,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ r2_hidden(X172,k5_relat_1(sK3,sK4)) )
    | ~ spl9_416 ),
    inference(avatar_component_clause,[],[f8642])).

fof(f8677,plain,
    ( ~ spl9_17
    | ~ spl9_59
    | spl9_428
    | ~ spl9_12
    | ~ spl9_306 ),
    inference(avatar_split_clause,[],[f5452,f5427,f167,f8673,f353,f178])).

fof(f353,plain,
    ( spl9_59
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f8673,plain,
    ( spl9_428
  <=> ! [X81] : ~ r2_hidden(X81,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_428])])).

fof(f5452,plain,
    ( ! [X138] :
        ( ~ r2_hidden(X138,k5_relat_1(sK3,sK3))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ v1_funct_1(sK3) )
    | ~ spl9_12
    | ~ spl9_306 ),
    inference(resolution,[],[f5428,f168])).

fof(f8676,plain,
    ( spl9_428
    | ~ spl9_17
    | ~ spl9_59
    | ~ spl9_40
    | ~ spl9_306 ),
    inference(avatar_split_clause,[],[f5482,f5427,f273,f353,f178,f8673])).

fof(f5482,plain,
    ( ! [X81] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ v1_funct_1(sK3)
        | ~ r2_hidden(X81,k5_relat_1(sK3,sK3)) )
    | ~ spl9_40
    | ~ spl9_306 ),
    inference(resolution,[],[f5434,f274])).

fof(f8675,plain,
    ( ~ spl9_59
    | spl9_428
    | ~ spl9_17
    | ~ spl9_40
    | ~ spl9_382 ),
    inference(avatar_split_clause,[],[f6063,f6045,f273,f178,f8673,f353])).

fof(f6045,plain,
    ( spl9_382
  <=> ! [X193,X195,X192,X194] :
        ( ~ v1_funct_1(X192)
        | ~ r1_tarski(X192,k2_zfmisc_1(X193,X195))
        | ~ r2_hidden(X194,k5_relat_1(X192,sK3))
        | ~ v1_xboole_0(k2_zfmisc_1(X193,u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_382])])).

fof(f6063,plain,
    ( ! [X81] :
        ( ~ v1_funct_1(sK3)
        | ~ r2_hidden(X81,k5_relat_1(sK3,sK3))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) )
    | ~ spl9_40
    | ~ spl9_382 ),
    inference(resolution,[],[f6046,f274])).

fof(f6046,plain,
    ( ! [X194,X192,X195,X193] :
        ( ~ r1_tarski(X192,k2_zfmisc_1(X193,X195))
        | ~ v1_funct_1(X192)
        | ~ r2_hidden(X194,k5_relat_1(X192,sK3))
        | ~ v1_xboole_0(k2_zfmisc_1(X193,u1_struct_0(sK2))) )
    | ~ spl9_382 ),
    inference(avatar_component_clause,[],[f6045])).

fof(f8671,plain,
    ( ~ spl9_17
    | ~ spl9_59
    | spl9_426
    | ~ spl9_12
    | ~ spl9_306 ),
    inference(avatar_split_clause,[],[f7404,f5427,f167,f8669,f353,f178])).

fof(f8669,plain,
    ( spl9_426
  <=> ! [X217,X215,X216] :
        ( ~ v1_funct_1(k5_relat_1(X215,sK3))
        | v1_xboole_0(k5_relat_1(sK3,k5_relat_1(X215,sK3)))
        | ~ v1_funct_1(X215)
        | ~ m1_subset_1(X215,k1_zfmisc_1(k2_zfmisc_1(X216,X217))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_426])])).

fof(f7404,plain,
    ( ! [X216,X215,X217] :
        ( ~ v1_funct_1(k5_relat_1(X215,sK3))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X215,k1_zfmisc_1(k2_zfmisc_1(X216,X217)))
        | ~ v1_funct_1(X215)
        | v1_xboole_0(k5_relat_1(sK3,k5_relat_1(X215,sK3))) )
    | ~ spl9_12
    | ~ spl9_306 ),
    inference(resolution,[],[f7375,f168])).

fof(f8667,plain,
    ( ~ spl9_59
    | ~ spl9_17
    | ~ spl9_113
    | spl9_424
    | ~ spl9_12
    | ~ spl9_398 ),
    inference(avatar_split_clause,[],[f7968,f7937,f167,f8665,f1030,f178,f353])).

fof(f8665,plain,
    ( spl9_424
  <=> v1_xboole_0(k5_relat_1(k5_relat_1(sK3,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_424])])).

fof(f7937,plain,
    ( spl9_398
  <=> ! [X217,X215,X216] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X215,u1_struct_0(sK2)))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X216,sK3),sK3))
        | ~ v1_funct_1(k5_relat_1(X216,sK3))
        | ~ v1_funct_1(X216)
        | ~ m1_subset_1(X216,k1_zfmisc_1(k2_zfmisc_1(X215,X217))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_398])])).

fof(f7968,plain,
    ( v1_xboole_0(k5_relat_1(k5_relat_1(sK3,sK3),sK3))
    | ~ v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
    | ~ spl9_12
    | ~ spl9_398 ),
    inference(resolution,[],[f7938,f168])).

fof(f7938,plain,
    ( ! [X216,X215,X217] :
        ( ~ m1_subset_1(X216,k1_zfmisc_1(k2_zfmisc_1(X215,X217)))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X216,sK3),sK3))
        | ~ v1_funct_1(k5_relat_1(X216,sK3))
        | ~ v1_funct_1(X216)
        | ~ v1_xboole_0(k2_zfmisc_1(X215,u1_struct_0(sK2))) )
    | ~ spl9_398 ),
    inference(avatar_component_clause,[],[f7937])).

fof(f8660,plain,
    ( ~ spl9_59
    | ~ spl9_17
    | ~ spl9_117
    | spl9_422
    | ~ spl9_12
    | ~ spl9_400 ),
    inference(avatar_split_clause,[],[f8000,f7941,f167,f8658,f1072,f178,f353])).

fof(f8658,plain,
    ( spl9_422
  <=> v1_xboole_0(k5_relat_1(k5_relat_1(sK3,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_422])])).

fof(f7941,plain,
    ( spl9_400
  <=> ! [X219,X220,X218] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X218,u1_struct_0(sK2)))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X219,sK4),sK3))
        | ~ v1_funct_1(k5_relat_1(X219,sK4))
        | ~ v1_funct_1(X219)
        | ~ m1_subset_1(X219,k1_zfmisc_1(k2_zfmisc_1(X218,X220))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_400])])).

fof(f8000,plain,
    ( v1_xboole_0(k5_relat_1(k5_relat_1(sK3,sK4),sK3))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK3)
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
    | ~ spl9_12
    | ~ spl9_400 ),
    inference(resolution,[],[f7942,f168])).

fof(f7942,plain,
    ( ! [X218,X220,X219] :
        ( ~ m1_subset_1(X219,k1_zfmisc_1(k2_zfmisc_1(X218,X220)))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X219,sK4),sK3))
        | ~ v1_funct_1(k5_relat_1(X219,sK4))
        | ~ v1_funct_1(X219)
        | ~ v1_xboole_0(k2_zfmisc_1(X218,u1_struct_0(sK2))) )
    | ~ spl9_400 ),
    inference(avatar_component_clause,[],[f7941])).

fof(f8653,plain,
    ( ~ spl9_17
    | ~ spl9_59
    | spl9_420
    | ~ spl9_12
    | ~ spl9_382 ),
    inference(avatar_split_clause,[],[f8032,f6045,f167,f8651,f353,f178])).

fof(f8651,plain,
    ( spl9_420
  <=> ! [X217,X215,X216] :
        ( ~ v1_funct_1(X215)
        | ~ r1_tarski(X215,k2_zfmisc_1(X216,X217))
        | v1_xboole_0(k5_relat_1(k5_relat_1(sK3,X215),sK3))
        | ~ v1_funct_1(k5_relat_1(sK3,X215)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_420])])).

fof(f8032,plain,
    ( ! [X216,X215,X217] :
        ( ~ v1_funct_1(X215)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(k5_relat_1(sK3,X215))
        | v1_xboole_0(k5_relat_1(k5_relat_1(sK3,X215),sK3))
        | ~ r1_tarski(X215,k2_zfmisc_1(X216,X217)) )
    | ~ spl9_12
    | ~ spl9_382 ),
    inference(resolution,[],[f7904,f168])).

fof(f7904,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ v1_funct_1(X1)
        | ~ v1_xboole_0(k2_zfmisc_1(X0,u1_struct_0(sK2)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(k5_relat_1(X2,X1))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X2,X1),sK3))
        | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_382 ),
    inference(resolution,[],[f7897,f106])).

fof(f7897,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_xboole_0(k2_zfmisc_1(X2,u1_struct_0(sK2)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(X0,X1))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X0,X1),sK3)) )
    | ~ spl9_382 ),
    inference(resolution,[],[f6054,f280])).

fof(f6054,plain,
    ( ! [X14,X19,X17,X15,X13,X18,X16] :
        ( ~ r2_hidden(X15,k5_relat_1(k5_relat_1(X13,X14),sK3))
        | ~ v1_funct_1(k5_relat_1(X13,X14))
        | ~ v1_xboole_0(k2_zfmisc_1(X16,u1_struct_0(sK2)))
        | ~ v1_funct_1(X14)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
    | ~ spl9_382 ),
    inference(resolution,[],[f6046,f2800])).

fof(f8649,plain,
    ( spl9_58
    | spl9_418
    | ~ spl9_414 ),
    inference(avatar_split_clause,[],[f8645,f8638,f8647,f350])).

fof(f350,plain,
    ( spl9_58
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f8638,plain,
    ( spl9_414
  <=> ! [X171] :
        ( ~ r2_hidden(X171,k5_relat_1(sK3,sK3))
        | m1_subset_1(X171,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_414])])).

fof(f8645,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_relat_1(sK3,sK3))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) )
    | ~ spl9_414 ),
    inference(resolution,[],[f8639,f103])).

fof(f8639,plain,
    ( ! [X171] :
        ( m1_subset_1(X171,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ r2_hidden(X171,k5_relat_1(sK3,sK3)) )
    | ~ spl9_414 ),
    inference(avatar_component_clause,[],[f8638])).

fof(f8644,plain,
    ( ~ spl9_11
    | spl9_416
    | ~ spl9_6
    | ~ spl9_410 ),
    inference(avatar_split_clause,[],[f8628,f8598,f146,f8642,f157])).

fof(f8598,plain,
    ( spl9_410
  <=> ! [X238,X240,X237,X239] :
        ( ~ v1_funct_1(X237)
        | ~ r2_hidden(X240,k5_relat_1(sK3,X237))
        | m1_subset_1(X240,k2_zfmisc_1(u1_struct_0(sK0),X239))
        | ~ m1_subset_1(X237,k1_zfmisc_1(k2_zfmisc_1(X238,X239))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_410])])).

fof(f8628,plain,
    ( ! [X172] :
        ( ~ r2_hidden(X172,k5_relat_1(sK3,sK4))
        | m1_subset_1(X172,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_6
    | ~ spl9_410 ),
    inference(resolution,[],[f8599,f147])).

fof(f8599,plain,
    ( ! [X239,X237,X240,X238] :
        ( ~ m1_subset_1(X237,k1_zfmisc_1(k2_zfmisc_1(X238,X239)))
        | ~ r2_hidden(X240,k5_relat_1(sK3,X237))
        | m1_subset_1(X240,k2_zfmisc_1(u1_struct_0(sK0),X239))
        | ~ v1_funct_1(X237) )
    | ~ spl9_410 ),
    inference(avatar_component_clause,[],[f8598])).

fof(f8640,plain,
    ( ~ spl9_17
    | spl9_414
    | ~ spl9_12
    | ~ spl9_410 ),
    inference(avatar_split_clause,[],[f8627,f8598,f167,f8638,f178])).

fof(f8627,plain,
    ( ! [X171] :
        ( ~ r2_hidden(X171,k5_relat_1(sK3,sK3))
        | m1_subset_1(X171,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ v1_funct_1(sK3) )
    | ~ spl9_12
    | ~ spl9_410 ),
    inference(resolution,[],[f8599,f168])).

fof(f8604,plain,
    ( ~ spl9_11
    | spl9_412
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f8588,f146,f8602,f157])).

fof(f8588,plain,
    ( ! [X243,X241,X244,X242] :
        ( ~ v1_funct_1(X241)
        | ~ m1_subset_1(X241,k1_zfmisc_1(k2_zfmisc_1(X242,X243)))
        | ~ v1_funct_1(sK4)
        | m1_subset_1(X244,k2_zfmisc_1(u1_struct_0(sK2),X243))
        | ~ r2_hidden(X244,k5_relat_1(sK4,X241)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f2798,f147])).

fof(f8600,plain,
    ( ~ spl9_17
    | spl9_410
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f8587,f167,f8598,f178])).

fof(f8587,plain,
    ( ! [X239,X237,X240,X238] :
        ( ~ v1_funct_1(X237)
        | ~ m1_subset_1(X237,k1_zfmisc_1(k2_zfmisc_1(X238,X239)))
        | ~ v1_funct_1(sK3)
        | m1_subset_1(X240,k2_zfmisc_1(u1_struct_0(sK0),X239))
        | ~ r2_hidden(X240,k5_relat_1(sK3,X237)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f2798,f168])).

fof(f8564,plain,
    ( ~ spl9_23
    | spl9_408
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f8550,f5674,f8562,f199])).

fof(f8562,plain,
    ( spl9_408
  <=> ! [X5,X7,X4,X6] :
        ( v5_pre_topc(k8_relset_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5,X6,X7),X4,sK1)
        | ~ v4_pre_topc(sK5(X4,sK1,k8_relset_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5,X6,X7)),sK1)
        | v4_pre_topc(k10_relat_1(sK4,sK5(X4,sK1,k8_relset_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5,X6,X7))),sK2)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5)))
        | ~ l1_pre_topc(X4)
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5,X6,X7))
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5,X6,X7),u1_struct_0(X4),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_408])])).

fof(f8550,plain,
    ( ! [X6,X4,X7,X5] :
        ( v5_pre_topc(k8_relset_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5,X6,X7),X4,sK1)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5,X6,X7),u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5,X6,X7))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5)))
        | v4_pre_topc(k10_relat_1(sK4,sK5(X4,sK1,k8_relset_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5,X6,X7))),sK2)
        | ~ v4_pre_topc(sK5(X4,sK1,k8_relset_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)),X5,X6,X7)),sK1) )
    | ~ spl9_320 ),
    inference(resolution,[],[f1588,f5675])).

fof(f1588,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( m1_subset_1(sK5(X9,X10,k8_relset_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)),X11,X12,X13)),k1_zfmisc_1(u1_struct_0(X10)))
      | v5_pre_topc(k8_relset_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)),X11,X12,X13),X9,X10)
      | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)),X11,X12,X13),u1_struct_0(X9),u1_struct_0(X10))
      | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)),X11,X12,X13))
      | ~ l1_pre_topc(X10)
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10)),X11))) ) ),
    inference(resolution,[],[f95,f112])).

fof(f8560,plain,
    ( ~ spl9_19
    | spl9_406
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f8549,f5670,f8558,f185])).

fof(f8558,plain,
    ( spl9_406
  <=> ! [X1,X3,X0,X2] :
        ( v5_pre_topc(k8_relset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1,X2,X3),X0,sK2)
        | ~ v4_pre_topc(sK5(X0,sK2,k8_relset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1,X2,X3)),sK2)
        | v4_pre_topc(k10_relat_1(sK3,sK5(X0,sK2,k8_relset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1,X2,X3))),sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1)))
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1,X2,X3))
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1,X2,X3),u1_struct_0(X0),u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_406])])).

fof(f8549,plain,
    ( ! [X2,X0,X3,X1] :
        ( v5_pre_topc(k8_relset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1,X2,X3),X0,sK2)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1,X2,X3),u1_struct_0(X0),u1_struct_0(sK2))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1,X2,X3))
        | ~ l1_pre_topc(sK2)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1)))
        | v4_pre_topc(k10_relat_1(sK3,sK5(X0,sK2,k8_relset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1,X2,X3))),sK0)
        | ~ v4_pre_topc(sK5(X0,sK2,k8_relset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)),X1,X2,X3)),sK2) )
    | ~ spl9_318 ),
    inference(resolution,[],[f1588,f5671])).

fof(f8264,plain,
    ( ~ spl9_11
    | spl9_404
    | ~ spl9_6
    | ~ spl9_384 ),
    inference(avatar_split_clause,[],[f8248,f6049,f146,f8262,f157])).

fof(f8248,plain,
    ( ! [X218,X220,X219] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X218,u1_struct_0(sK1)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X219,k1_zfmisc_1(k2_zfmisc_1(X218,X220)))
        | ~ v1_funct_1(X219)
        | ~ v1_funct_1(k5_relat_1(X219,sK4))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X219,sK4),sK4)) )
    | ~ spl9_6
    | ~ spl9_384 ),
    inference(resolution,[],[f8218,f147])).

fof(f8260,plain,
    ( ~ spl9_17
    | spl9_402
    | ~ spl9_12
    | ~ spl9_384 ),
    inference(avatar_split_clause,[],[f8247,f6049,f167,f8258,f178])).

fof(f8247,plain,
    ( ! [X216,X215,X217] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X215,u1_struct_0(sK1)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X216,k1_zfmisc_1(k2_zfmisc_1(X215,X217)))
        | ~ v1_funct_1(X216)
        | ~ v1_funct_1(k5_relat_1(X216,sK3))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X216,sK3),sK4)) )
    | ~ spl9_12
    | ~ spl9_384 ),
    inference(resolution,[],[f8218,f168])).

fof(f7943,plain,
    ( ~ spl9_11
    | spl9_400
    | ~ spl9_6
    | ~ spl9_382 ),
    inference(avatar_split_clause,[],[f7927,f6045,f146,f7941,f157])).

fof(f7927,plain,
    ( ! [X218,X220,X219] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X218,u1_struct_0(sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X219,k1_zfmisc_1(k2_zfmisc_1(X218,X220)))
        | ~ v1_funct_1(X219)
        | ~ v1_funct_1(k5_relat_1(X219,sK4))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X219,sK4),sK3)) )
    | ~ spl9_6
    | ~ spl9_382 ),
    inference(resolution,[],[f7897,f147])).

fof(f7939,plain,
    ( ~ spl9_17
    | spl9_398
    | ~ spl9_12
    | ~ spl9_382 ),
    inference(avatar_split_clause,[],[f7926,f6045,f167,f7937,f178])).

fof(f7926,plain,
    ( ! [X216,X215,X217] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X215,u1_struct_0(sK2)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X216,k1_zfmisc_1(k2_zfmisc_1(X215,X217)))
        | ~ v1_funct_1(X216)
        | ~ v1_funct_1(k5_relat_1(X216,sK3))
        | v1_xboole_0(k5_relat_1(k5_relat_1(X216,sK3),sK3)) )
    | ~ spl9_12
    | ~ spl9_382 ),
    inference(resolution,[],[f7897,f168])).

fof(f7658,plain,
    ( ~ spl9_11
    | spl9_396
    | ~ spl9_6
    | ~ spl9_308 ),
    inference(avatar_split_clause,[],[f7642,f5431,f146,f7656,f157])).

fof(f7656,plain,
    ( spl9_396
  <=> ! [X219,X220,X218] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X218))
        | ~ v1_funct_1(X219)
        | ~ r1_tarski(X219,k2_zfmisc_1(X220,X218))
        | v1_xboole_0(k5_relat_1(sK4,k5_relat_1(sK4,X219)))
        | ~ v1_funct_1(k5_relat_1(sK4,X219)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_396])])).

fof(f7642,plain,
    ( ! [X218,X220,X219] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X218))
        | ~ v1_funct_1(X219)
        | ~ v1_funct_1(k5_relat_1(sK4,X219))
        | ~ v1_funct_1(sK4)
        | v1_xboole_0(k5_relat_1(sK4,k5_relat_1(sK4,X219)))
        | ~ r1_tarski(X219,k2_zfmisc_1(X220,X218)) )
    | ~ spl9_6
    | ~ spl9_308 ),
    inference(resolution,[],[f7587,f147])).

fof(f7587,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(k5_relat_1(X0,X1))
        | ~ v1_funct_1(X0)
        | v1_xboole_0(k5_relat_1(sK4,k5_relat_1(X0,X1)))
        | ~ r1_tarski(X1,k2_zfmisc_1(X5,X2)) )
    | ~ spl9_308 ),
    inference(resolution,[],[f7580,f106])).

fof(f7654,plain,
    ( ~ spl9_17
    | spl9_394
    | ~ spl9_12
    | ~ spl9_308 ),
    inference(avatar_split_clause,[],[f7641,f5431,f167,f7652,f178])).

fof(f7652,plain,
    ( spl9_394
  <=> ! [X217,X215,X216] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X215))
        | ~ v1_funct_1(X216)
        | ~ r1_tarski(X216,k2_zfmisc_1(X217,X215))
        | v1_xboole_0(k5_relat_1(sK4,k5_relat_1(sK3,X216)))
        | ~ v1_funct_1(k5_relat_1(sK3,X216)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_394])])).

fof(f7641,plain,
    ( ! [X216,X215,X217] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X215))
        | ~ v1_funct_1(X216)
        | ~ v1_funct_1(k5_relat_1(sK3,X216))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(k5_relat_1(sK4,k5_relat_1(sK3,X216)))
        | ~ r1_tarski(X216,k2_zfmisc_1(X217,X215)) )
    | ~ spl9_12
    | ~ spl9_308 ),
    inference(resolution,[],[f7587,f168])).

fof(f7453,plain,
    ( ~ spl9_11
    | spl9_392
    | ~ spl9_6
    | ~ spl9_306 ),
    inference(avatar_split_clause,[],[f7437,f5427,f146,f7451,f157])).

fof(f7451,plain,
    ( spl9_392
  <=> ! [X219,X220,X218] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X218))
        | ~ v1_funct_1(X219)
        | ~ r1_tarski(X219,k2_zfmisc_1(X220,X218))
        | v1_xboole_0(k5_relat_1(sK3,k5_relat_1(sK4,X219)))
        | ~ v1_funct_1(k5_relat_1(sK4,X219)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_392])])).

fof(f7437,plain,
    ( ! [X218,X220,X219] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X218))
        | ~ v1_funct_1(X219)
        | ~ v1_funct_1(k5_relat_1(sK4,X219))
        | ~ v1_funct_1(sK4)
        | v1_xboole_0(k5_relat_1(sK3,k5_relat_1(sK4,X219)))
        | ~ r1_tarski(X219,k2_zfmisc_1(X220,X218)) )
    | ~ spl9_6
    | ~ spl9_306 ),
    inference(resolution,[],[f7382,f147])).

fof(f7382,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(k5_relat_1(X0,X1))
        | ~ v1_funct_1(X0)
        | v1_xboole_0(k5_relat_1(sK3,k5_relat_1(X0,X1)))
        | ~ r1_tarski(X1,k2_zfmisc_1(X5,X2)) )
    | ~ spl9_306 ),
    inference(resolution,[],[f7375,f106])).

fof(f7449,plain,
    ( ~ spl9_17
    | spl9_390
    | ~ spl9_12
    | ~ spl9_306 ),
    inference(avatar_split_clause,[],[f7436,f5427,f167,f7447,f178])).

fof(f7447,plain,
    ( spl9_390
  <=> ! [X217,X215,X216] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X215))
        | ~ v1_funct_1(X216)
        | ~ r1_tarski(X216,k2_zfmisc_1(X217,X215))
        | v1_xboole_0(k5_relat_1(sK3,k5_relat_1(sK3,X216)))
        | ~ v1_funct_1(k5_relat_1(sK3,X216)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_390])])).

fof(f7436,plain,
    ( ! [X216,X215,X217] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X215))
        | ~ v1_funct_1(X216)
        | ~ v1_funct_1(k5_relat_1(sK3,X216))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(k5_relat_1(sK3,k5_relat_1(sK3,X216)))
        | ~ r1_tarski(X216,k2_zfmisc_1(X217,X215)) )
    | ~ spl9_12
    | ~ spl9_306 ),
    inference(resolution,[],[f7382,f168])).

fof(f6929,plain,
    ( ~ spl9_23
    | spl9_388
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f6917,f5674,f6927,f199])).

fof(f6927,plain,
    ( spl9_388
  <=> ! [X1] :
        ( v5_pre_topc(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))),X1,sK1)
        | ~ v4_pre_topc(sK5(X1,sK1,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))),sK1)
        | v4_pre_topc(k10_relat_1(sK4,sK5(X1,sK1,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))))),sK2)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))),u1_struct_0(X1),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_388])])).

fof(f6917,plain,
    ( ! [X1] :
        ( v5_pre_topc(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))),X1,sK1)
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))),u1_struct_0(X1),u1_struct_0(sK1))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))))
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X1)
        | v4_pre_topc(k10_relat_1(sK4,sK5(X1,sK1,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))))),sK2)
        | ~ v4_pre_topc(sK5(X1,sK1,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))),sK1) )
    | ~ spl9_320 ),
    inference(resolution,[],[f1600,f5675])).

fof(f1600,plain,(
    ! [X70,X71] :
      ( m1_subset_1(sK5(X70,X71,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X70),u1_struct_0(X71))))),k1_zfmisc_1(u1_struct_0(X71)))
      | v5_pre_topc(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X70),u1_struct_0(X71)))),X70,X71)
      | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X70),u1_struct_0(X71)))),u1_struct_0(X70),u1_struct_0(X71))
      | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X70),u1_struct_0(X71)))))
      | ~ l1_pre_topc(X71)
      | ~ l1_pre_topc(X70) ) ),
    inference(resolution,[],[f95,f99])).

fof(f6925,plain,
    ( ~ spl9_19
    | spl9_386
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f6916,f5670,f6923,f185])).

fof(f6923,plain,
    ( spl9_386
  <=> ! [X0] :
        ( v5_pre_topc(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))),X0,sK2)
        | ~ v4_pre_topc(sK5(X0,sK2,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))),sK2)
        | v4_pre_topc(k10_relat_1(sK3,sK5(X0,sK2,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))))),sK0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))),u1_struct_0(X0),u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_386])])).

fof(f6916,plain,
    ( ! [X0] :
        ( v5_pre_topc(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))),X0,sK2)
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))),u1_struct_0(X0),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))))
        | ~ l1_pre_topc(sK2)
        | ~ l1_pre_topc(X0)
        | v4_pre_topc(k10_relat_1(sK3,sK5(X0,sK2,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))))),sK0)
        | ~ v4_pre_topc(sK5(X0,sK2,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))),sK2) )
    | ~ spl9_318 ),
    inference(resolution,[],[f1600,f5671])).

fof(f6051,plain,
    ( spl9_384
    | ~ spl9_11
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f6036,f146,f157,f6049])).

fof(f6036,plain,
    ( ! [X198,X196,X199,X197] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_1(X196)
        | ~ v1_xboole_0(k2_zfmisc_1(X197,u1_struct_0(sK1)))
        | ~ r2_hidden(X198,k5_relat_1(X196,sK4))
        | ~ r1_tarski(X196,k2_zfmisc_1(X197,X199)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f5399,f147])).

fof(f6047,plain,
    ( spl9_382
    | ~ spl9_17
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f6035,f167,f178,f6045])).

fof(f6035,plain,
    ( ! [X194,X192,X195,X193] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X192)
        | ~ v1_xboole_0(k2_zfmisc_1(X193,u1_struct_0(sK2)))
        | ~ r2_hidden(X194,k5_relat_1(X192,sK3))
        | ~ r1_tarski(X192,k2_zfmisc_1(X193,X195)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f5399,f168])).

fof(f5945,plain,
    ( ~ spl9_23
    | spl9_380
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f5941,f5674,f5943,f199])).

fof(f5943,plain,
    ( spl9_380
  <=> ! [X1,X0,X2] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(X0,X1)),sK2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X2))
        | ~ v5_pre_topc(X0,sK1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v4_pre_topc(X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_380])])).

fof(f5941,plain,
    ( ! [X2,X0,X1] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(X0,X1)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
        | ~ v4_pre_topc(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v5_pre_topc(X0,sK1,X2)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X2)
        | ~ l1_pre_topc(sK1) )
    | ~ spl9_320 ),
    inference(duplicate_literal_removal,[],[f5938])).

fof(f5938,plain,
    ( ! [X2,X0,X1] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(X0,X1)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
        | ~ v4_pre_topc(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v5_pre_topc(X0,sK1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X2)
        | ~ l1_pre_topc(sK1) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5937,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f5937,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK1),X0,X1,X2),sK1)
        | v4_pre_topc(k10_relat_1(sK4,k10_relat_1(X1,X2)),sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))) )
    | ~ spl9_320 ),
    inference(duplicate_literal_removal,[],[f5936])).

fof(f5936,plain,
    ( ! [X2,X0,X1] :
        ( v4_pre_topc(k10_relat_1(sK4,k10_relat_1(X1,X2)),sK2)
        | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK1),X0,X1,X2),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))) )
    | ~ spl9_320 ),
    inference(superposition,[],[f5788,f113])).

fof(f5788,plain,
    ( ! [X2,X3,X1] :
        ( v4_pre_topc(k10_relat_1(sK4,k8_relset_1(u1_struct_0(sK1),X1,X2,X3)),sK2)
        | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK1),X1,X2,X3),sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1))) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f112])).

fof(f5909,plain,
    ( ~ spl9_19
    | spl9_378
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f5905,f5670,f5907,f185])).

fof(f5907,plain,
    ( spl9_378
  <=> ! [X1,X0,X2] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(X0,X1)),sK0)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v5_pre_topc(X0,sK2,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v4_pre_topc(X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_378])])).

fof(f5905,plain,
    ( ! [X2,X0,X1] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(X0,X1)),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | ~ v4_pre_topc(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v5_pre_topc(X0,sK2,X2)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X2)
        | ~ l1_pre_topc(sK2) )
    | ~ spl9_318 ),
    inference(duplicate_literal_removal,[],[f5902])).

fof(f5902,plain,
    ( ! [X2,X0,X1] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(X0,X1)),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | ~ v4_pre_topc(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v5_pre_topc(X0,sK2,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X2)
        | ~ l1_pre_topc(sK2) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5901,f94])).

fof(f5901,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),X0,X1,X2),sK2)
        | v4_pre_topc(k10_relat_1(sK3,k10_relat_1(X1,X2)),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0))) )
    | ~ spl9_318 ),
    inference(duplicate_literal_removal,[],[f5900])).

fof(f5900,plain,
    ( ! [X2,X0,X1] :
        ( v4_pre_topc(k10_relat_1(sK3,k10_relat_1(X1,X2)),sK0)
        | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),X0,X1,X2),sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0))) )
    | ~ spl9_318 ),
    inference(superposition,[],[f5678,f113])).

fof(f5678,plain,
    ( ! [X2,X3,X1] :
        ( v4_pre_topc(k10_relat_1(sK3,k8_relset_1(u1_struct_0(sK2),X1,X2,X3)),sK0)
        | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),X1,X2,X3),sK2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f112])).

fof(f5895,plain,
    ( ~ spl9_19
    | ~ spl9_11
    | spl9_376
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f5891,f5674,f5893,f157,f185])).

fof(f5893,plain,
    ( spl9_376
  <=> ! [X0] :
        ( ~ v4_pre_topc(sK5(sK2,X0,sK4),sK1)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | v5_pre_topc(sK4,sK2,X0)
        | ~ r1_tarski(sK5(sK2,X0,sK4),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_376])])).

fof(f5891,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(sK5(sK2,X0,sK4),sK1)
        | ~ r1_tarski(sK5(sK2,X0,sK4),u1_struct_0(sK1))
        | v5_pre_topc(sK4,sK2,X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK2) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5787,f2198])).

fof(f5890,plain,
    ( spl9_368
    | spl9_370
    | ~ spl9_373
    | spl9_374
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f5809,f5674,f5888,f5882,f5876,f5870])).

fof(f5870,plain,
    ( spl9_368
  <=> v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_368])])).

fof(f5876,plain,
    ( spl9_370
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_370])])).

fof(f5882,plain,
    ( spl9_373
  <=> ~ v4_pre_topc(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_373])])).

fof(f5888,plain,
    ( spl9_374
  <=> v4_pre_topc(k10_relat_1(sK4,sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_374])])).

fof(f5809,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))),sK2)
    | ~ v4_pre_topc(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))),sK1)
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))
    | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f661])).

fof(f5865,plain,
    ( spl9_356
    | spl9_362
    | ~ spl9_365
    | spl9_366
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f5808,f5674,f5863,f5857,f5851,f5832])).

fof(f5851,plain,
    ( spl9_362
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_362])])).

fof(f5857,plain,
    ( spl9_365
  <=> ~ v4_pre_topc(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_365])])).

fof(f5863,plain,
    ( spl9_366
  <=> v4_pre_topc(k10_relat_1(sK4,sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_366])])).

fof(f5808,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))),sK2)
    | ~ v4_pre_topc(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))),sK1)
    | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f455])).

fof(f5846,plain,
    ( spl9_356
    | ~ spl9_359
    | spl9_360
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f5807,f5674,f5844,f5838,f5832])).

fof(f5838,plain,
    ( spl9_359
  <=> ~ v4_pre_topc(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_359])])).

fof(f5844,plain,
    ( spl9_360
  <=> v4_pre_topc(k10_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_360])])).

fof(f5807,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))),sK2)
    | ~ v4_pre_topc(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),sK1)
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f374])).

fof(f5827,plain,
    ( ~ spl9_353
    | spl9_354
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f5804,f5674,f5825,f5819])).

fof(f5819,plain,
    ( spl9_353
  <=> ~ v4_pre_topc(sK6(k1_zfmisc_1(u1_struct_0(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_353])])).

fof(f5825,plain,
    ( spl9_354
  <=> v4_pre_topc(k10_relat_1(sK4,sK6(k1_zfmisc_1(u1_struct_0(sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_354])])).

fof(f5804,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK6(k1_zfmisc_1(u1_struct_0(sK1)))),sK2)
    | ~ v4_pre_topc(sK6(k1_zfmisc_1(u1_struct_0(sK1))),sK1)
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f99])).

fof(f5814,plain,
    ( ~ spl9_23
    | spl9_350
    | ~ spl9_320 ),
    inference(avatar_split_clause,[],[f5803,f5674,f5812,f199])).

fof(f5803,plain,
    ( ! [X76,X77] :
        ( v4_pre_topc(k10_relat_1(sK4,sK5(X76,sK1,X77)),sK2)
        | ~ v4_pre_topc(sK5(X76,sK1,X77),sK1)
        | v5_pre_topc(X77,X76,sK1)
        | ~ v1_funct_2(X77,u1_struct_0(X76),u1_struct_0(sK1))
        | ~ v1_funct_1(X77)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X76)
        | ~ r1_tarski(X77,k2_zfmisc_1(u1_struct_0(X76),u1_struct_0(sK1))) )
    | ~ spl9_320 ),
    inference(resolution,[],[f5675,f1586])).

fof(f5786,plain,
    ( ~ spl9_25
    | ~ spl9_17
    | spl9_348
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f5782,f5670,f5784,f178,f206])).

fof(f5784,plain,
    ( spl9_348
  <=> ! [X0] :
        ( ~ v4_pre_topc(sK5(sK0,X0,sK3),sK2)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | v5_pre_topc(sK3,sK0,X0)
        | ~ r1_tarski(sK5(sK0,X0,sK3),u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_348])])).

fof(f5782,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(sK5(sK0,X0,sK3),sK2)
        | ~ r1_tarski(sK5(sK0,X0,sK3),u1_struct_0(sK2))
        | v5_pre_topc(sK3,sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(sK3)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5677,f2198])).

fof(f5781,plain,
    ( spl9_340
    | spl9_342
    | ~ spl9_345
    | spl9_346
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f5700,f5670,f5779,f5773,f5767,f5761])).

fof(f5761,plain,
    ( spl9_340
  <=> v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_340])])).

fof(f5767,plain,
    ( spl9_342
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_342])])).

fof(f5773,plain,
    ( spl9_345
  <=> ~ v4_pre_topc(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_345])])).

fof(f5779,plain,
    ( spl9_346
  <=> v4_pre_topc(k10_relat_1(sK3,sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_346])])).

fof(f5700,plain,
    ( v4_pre_topc(k10_relat_1(sK3,sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))))),sK0)
    | ~ v4_pre_topc(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))))),sK2)
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))))
    | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))))
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f661])).

fof(f5756,plain,
    ( spl9_328
    | spl9_334
    | ~ spl9_337
    | spl9_338
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f5699,f5670,f5754,f5748,f5742,f5723])).

fof(f5742,plain,
    ( spl9_334
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_334])])).

fof(f5748,plain,
    ( spl9_337
  <=> ~ v4_pre_topc(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_337])])).

fof(f5754,plain,
    ( spl9_338
  <=> v4_pre_topc(k10_relat_1(sK3,sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_338])])).

fof(f5699,plain,
    ( v4_pre_topc(k10_relat_1(sK3,sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))))),sK0)
    | ~ v4_pre_topc(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))))),sK2)
    | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))))
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f455])).

fof(f5737,plain,
    ( spl9_328
    | ~ spl9_331
    | spl9_332
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f5698,f5670,f5735,f5729,f5723])).

fof(f5729,plain,
    ( spl9_331
  <=> ~ v4_pre_topc(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_331])])).

fof(f5735,plain,
    ( spl9_332
  <=> v4_pre_topc(k10_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_332])])).

fof(f5698,plain,
    ( v4_pre_topc(k10_relat_1(sK3,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),sK0)
    | ~ v4_pre_topc(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),sK2)
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f374])).

fof(f5718,plain,
    ( ~ spl9_325
    | spl9_326
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f5695,f5670,f5716,f5710])).

fof(f5710,plain,
    ( spl9_325
  <=> ~ v4_pre_topc(sK6(k1_zfmisc_1(u1_struct_0(sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_325])])).

fof(f5716,plain,
    ( spl9_326
  <=> v4_pre_topc(k10_relat_1(sK3,sK6(k1_zfmisc_1(u1_struct_0(sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_326])])).

fof(f5695,plain,
    ( v4_pre_topc(k10_relat_1(sK3,sK6(k1_zfmisc_1(u1_struct_0(sK2)))),sK0)
    | ~ v4_pre_topc(sK6(k1_zfmisc_1(u1_struct_0(sK2))),sK2)
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f99])).

fof(f5705,plain,
    ( ~ spl9_19
    | spl9_322
    | ~ spl9_318 ),
    inference(avatar_split_clause,[],[f5694,f5670,f5703,f185])).

fof(f5703,plain,
    ( spl9_322
  <=> ! [X77,X78] :
        ( v4_pre_topc(k10_relat_1(sK3,sK5(X77,sK2,X78)),sK0)
        | ~ r1_tarski(X78,k2_zfmisc_1(u1_struct_0(X77),u1_struct_0(sK2)))
        | ~ l1_pre_topc(X77)
        | ~ v1_funct_1(X78)
        | ~ v1_funct_2(X78,u1_struct_0(X77),u1_struct_0(sK2))
        | v5_pre_topc(X78,X77,sK2)
        | ~ v4_pre_topc(sK5(X77,sK2,X78),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_322])])).

fof(f5694,plain,
    ( ! [X78,X77] :
        ( v4_pre_topc(k10_relat_1(sK3,sK5(X77,sK2,X78)),sK0)
        | ~ v4_pre_topc(sK5(X77,sK2,X78),sK2)
        | v5_pre_topc(X78,X77,sK2)
        | ~ v1_funct_2(X78,u1_struct_0(X77),u1_struct_0(sK2))
        | ~ v1_funct_1(X78)
        | ~ l1_pre_topc(sK2)
        | ~ l1_pre_topc(X77)
        | ~ r1_tarski(X78,k2_zfmisc_1(u1_struct_0(X77),u1_struct_0(sK2))) )
    | ~ spl9_318 ),
    inference(resolution,[],[f5671,f1586])).

fof(f5676,plain,
    ( ~ spl9_19
    | ~ spl9_23
    | ~ spl9_11
    | ~ spl9_9
    | ~ spl9_3
    | spl9_320
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f5661,f146,f5674,f129,f150,f157,f199,f185])).

fof(f150,plain,
    ( spl9_9
  <=> ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f129,plain,
    ( spl9_3
  <=> ~ v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f5661,plain,
    ( ! [X139] :
        ( ~ v4_pre_topc(X139,sK1)
        | ~ m1_subset_1(X139,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(sK4,sK2,sK1)
        | v4_pre_topc(k10_relat_1(sK4,X139),sK2)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK2) )
    | ~ spl9_6 ),
    inference(resolution,[],[f2508,f147])).

fof(f2508,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(k10_relat_1(X2,X3),X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f2507])).

fof(f2507,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(k10_relat_1(X2,X3),X0)
      | ~ v4_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ),
    inference(superposition,[],[f94,f113])).

fof(f5672,plain,
    ( ~ spl9_25
    | ~ spl9_19
    | ~ spl9_17
    | ~ spl9_15
    | ~ spl9_5
    | spl9_318
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f5660,f167,f5670,f136,f171,f178,f185,f206])).

fof(f171,plain,
    ( spl9_15
  <=> ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f136,plain,
    ( spl9_5
  <=> ~ v5_pre_topc(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f5660,plain,
    ( ! [X138] :
        ( ~ v4_pre_topc(X138,sK2)
        | ~ m1_subset_1(X138,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v5_pre_topc(sK3,sK0,sK2)
        | v4_pre_topc(k10_relat_1(sK3,X138),sK0)
        | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v1_funct_1(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ l1_pre_topc(sK0) )
    | ~ spl9_12 ),
    inference(resolution,[],[f2508,f168])).

fof(f5526,plain,
    ( ~ spl9_17
    | ~ spl9_315
    | spl9_316
    | ~ spl9_12
    | ~ spl9_308 ),
    inference(avatar_split_clause,[],[f5508,f5431,f167,f5524,f5521,f178])).

fof(f5521,plain,
    ( spl9_315
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_315])])).

fof(f5524,plain,
    ( spl9_316
  <=> ! [X138] : ~ r2_hidden(X138,k5_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_316])])).

fof(f5508,plain,
    ( ! [X138] :
        ( ~ r2_hidden(X138,k5_relat_1(sK4,sK3))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
        | ~ v1_funct_1(sK3) )
    | ~ spl9_12
    | ~ spl9_308 ),
    inference(resolution,[],[f5432,f168])).

fof(f5470,plain,
    ( ~ spl9_11
    | ~ spl9_311
    | spl9_312
    | ~ spl9_6
    | ~ spl9_306 ),
    inference(avatar_split_clause,[],[f5453,f5427,f146,f5468,f5465,f157])).

fof(f5453,plain,
    ( ! [X139] :
        ( ~ r2_hidden(X139,k5_relat_1(sK3,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_6
    | ~ spl9_306 ),
    inference(resolution,[],[f5428,f147])).

fof(f5433,plain,
    ( ~ spl9_11
    | spl9_308
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f5418,f146,f5431,f157])).

fof(f5418,plain,
    ( ! [X198,X196,X199,X197] :
        ( ~ v1_funct_1(X196)
        | ~ m1_subset_1(X196,k1_zfmisc_1(k2_zfmisc_1(X197,X198)))
        | ~ v1_funct_1(sK4)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),X198))
        | ~ r2_hidden(X199,k5_relat_1(sK4,X196)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f2799,f147])).

fof(f5429,plain,
    ( ~ spl9_17
    | spl9_306
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f5417,f167,f5427,f178])).

fof(f5417,plain,
    ( ! [X194,X192,X195,X193] :
        ( ~ v1_funct_1(X192)
        | ~ m1_subset_1(X192,k1_zfmisc_1(k2_zfmisc_1(X193,X194)))
        | ~ v1_funct_1(sK3)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),X194))
        | ~ r2_hidden(X195,k5_relat_1(sK3,X192)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f2799,f168])).

fof(f5217,plain,
    ( spl9_82
    | spl9_304
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f5211,f146,f5215,f493])).

fof(f493,plain,
    ( spl9_82
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f5215,plain,
    ( spl9_304
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(k10_relat_1(sK4,X0))
        | r2_hidden(sK6(k8_relset_1(k10_relat_1(sK4,X0),X2,X1,X3)),u1_struct_0(sK2))
        | v1_xboole_0(k8_relset_1(k10_relat_1(sK4,X0),X2,X1,X3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK4,X0),X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_304])])).

fof(f5211,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(k10_relat_1(sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK4,X0),X2)))
        | v1_xboole_0(k8_relset_1(k10_relat_1(sK4,X0),X2,X1,X3))
        | v1_xboole_0(u1_struct_0(sK2))
        | r2_hidden(sK6(k8_relset_1(k10_relat_1(sK4,X0),X2,X1,X3)),u1_struct_0(sK2)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f2093,f103])).

fof(f2093,plain,
    ( ! [X37,X35,X36,X34] :
        ( m1_subset_1(sK6(k8_relset_1(k10_relat_1(sK4,X34),X35,X36,X37)),u1_struct_0(sK2))
        | v1_xboole_0(k10_relat_1(sK4,X34))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK4,X34),X35)))
        | v1_xboole_0(k8_relset_1(k10_relat_1(sK4,X34),X35,X36,X37)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f1258,f490])).

fof(f490,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(sK4,X1))
        | m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f475,f370])).

fof(f475,plain,
    ( ! [X11] : r1_tarski(k10_relat_1(sK4,X11),u1_struct_0(sK2))
    | ~ spl9_6 ),
    inference(resolution,[],[f471,f147])).

fof(f5174,plain,
    ( ~ spl9_11
    | spl9_302
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f5159,f146,f5172,f157])).

fof(f5172,plain,
    ( spl9_302
  <=> ! [X197,X199,X196,X198] :
        ( ~ v1_funct_1(X196)
        | ~ r1_tarski(X196,k2_zfmisc_1(X197,X199))
        | v1_xboole_0(k10_relat_1(k5_relat_1(X196,sK4),X198))
        | ~ v1_xboole_0(X197) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_302])])).

fof(f5159,plain,
    ( ! [X198,X196,X199,X197] :
        ( ~ v1_funct_1(X196)
        | ~ v1_funct_1(sK4)
        | ~ v1_xboole_0(X197)
        | v1_xboole_0(k10_relat_1(k5_relat_1(X196,sK4),X198))
        | ~ r1_tarski(X196,k2_zfmisc_1(X197,X199)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f5029,f147])).

fof(f5029,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_xboole_0(X4)
      | v1_xboole_0(k10_relat_1(k5_relat_1(X1,X0),X5))
      | ~ r1_tarski(X1,k2_zfmisc_1(X4,X6)) ) ),
    inference(resolution,[],[f3913,f106])).

fof(f3913,plain,(
    ! [X111,X116,X114,X112,X117,X115,X113] :
      ( ~ m1_subset_1(X112,k1_zfmisc_1(k2_zfmisc_1(X113,X114)))
      | ~ v1_funct_1(X111)
      | ~ v1_funct_1(X112)
      | ~ m1_subset_1(X111,k1_zfmisc_1(k2_zfmisc_1(X115,X116)))
      | ~ v1_xboole_0(X113)
      | v1_xboole_0(k10_relat_1(k5_relat_1(X112,X111),X117)) ) ),
    inference(resolution,[],[f2800,f781])).

fof(f781,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X0,X2))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k10_relat_1(X1,X3)) ) ),
    inference(duplicate_literal_removal,[],[f771])).

fof(f771,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r1_tarski(X1,k2_zfmisc_1(X0,X2))
      | v1_xboole_0(k10_relat_1(X1,X3))
      | ~ r1_tarski(X1,k2_zfmisc_1(X0,X2)) ) ),
    inference(resolution,[],[f660,f106])).

fof(f660,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | v1_xboole_0(k10_relat_1(X2,X3)) ) ),
    inference(superposition,[],[f650,f113])).

fof(f650,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(k8_relset_1(X0,X1,X2,X3))
      | ~ v1_xboole_0(X0)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f637,f106])).

fof(f637,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k8_relset_1(X0,X2,X1,X3)) ) ),
    inference(resolution,[],[f459,f280])).

fof(f459,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(X8,k8_relset_1(X6,X7,X5,X9))
      | ~ v1_xboole_0(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f112,f111])).

fof(f5170,plain,
    ( ~ spl9_17
    | spl9_300
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f5158,f167,f5168,f178])).

fof(f5168,plain,
    ( spl9_300
  <=> ! [X193,X195,X192,X194] :
        ( ~ v1_funct_1(X192)
        | ~ r1_tarski(X192,k2_zfmisc_1(X193,X195))
        | v1_xboole_0(k10_relat_1(k5_relat_1(X192,sK3),X194))
        | ~ v1_xboole_0(X193) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_300])])).

fof(f5158,plain,
    ( ! [X194,X192,X195,X193] :
        ( ~ v1_funct_1(X192)
        | ~ v1_funct_1(sK3)
        | ~ v1_xboole_0(X193)
        | v1_xboole_0(k10_relat_1(k5_relat_1(X192,sK3),X194))
        | ~ r1_tarski(X192,k2_zfmisc_1(X193,X195)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f5029,f168])).

fof(f5094,plain,
    ( ~ spl9_11
    | spl9_298
    | ~ spl9_6
    | ~ spl9_294 ),
    inference(avatar_split_clause,[],[f5079,f5057,f146,f5092,f157])).

fof(f5057,plain,
    ( spl9_294
  <=> ! [X193,X195,X192,X194] :
        ( ~ v1_funct_1(X192)
        | v1_xboole_0(k10_relat_1(k5_relat_1(sK3,X192),X195))
        | ~ m1_subset_1(X192,k1_zfmisc_1(k2_zfmisc_1(X193,X194))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_294])])).

fof(f5079,plain,
    ( ! [X139] :
        ( v1_xboole_0(k10_relat_1(k5_relat_1(sK3,sK4),X139))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_6
    | ~ spl9_294 ),
    inference(resolution,[],[f5058,f147])).

fof(f5058,plain,
    ( ! [X194,X192,X195,X193] :
        ( ~ m1_subset_1(X192,k1_zfmisc_1(k2_zfmisc_1(X193,X194)))
        | v1_xboole_0(k10_relat_1(k5_relat_1(sK3,X192),X195))
        | ~ v1_funct_1(X192) )
    | ~ spl9_294 ),
    inference(avatar_component_clause,[],[f5057])).

fof(f5090,plain,
    ( ~ spl9_17
    | spl9_296
    | ~ spl9_12
    | ~ spl9_294 ),
    inference(avatar_split_clause,[],[f5078,f5057,f167,f5088,f178])).

fof(f5078,plain,
    ( ! [X138] :
        ( v1_xboole_0(k10_relat_1(k5_relat_1(sK3,sK3),X138))
        | ~ v1_funct_1(sK3) )
    | ~ spl9_12
    | ~ spl9_294 ),
    inference(resolution,[],[f5058,f168])).

fof(f5059,plain,
    ( ~ spl9_79
    | ~ spl9_17
    | spl9_294
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f5047,f167,f5057,f178,f484])).

fof(f5047,plain,
    ( ! [X194,X192,X195,X193] :
        ( ~ v1_funct_1(X192)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X192,k1_zfmisc_1(k2_zfmisc_1(X193,X194)))
        | ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k10_relat_1(k5_relat_1(sK3,X192),X195)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f3913,f168])).

fof(f4696,plain,
    ( spl9_292
    | ~ spl9_33
    | ~ spl9_288 ),
    inference(avatar_split_clause,[],[f4689,f4683,f238,f4694])).

fof(f4694,plain,
    ( spl9_292
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_292])])).

fof(f238,plain,
    ( spl9_33
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f4683,plain,
    ( spl9_288
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_288])])).

fof(f4689,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_288 ),
    inference(resolution,[],[f4684,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',fc2_struct_0)).

fof(f4684,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl9_288 ),
    inference(avatar_component_clause,[],[f4683])).

fof(f4688,plain,
    ( spl9_288
    | ~ spl9_11
    | ~ spl9_9
    | spl9_290
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f4667,f146,f4686,f150,f157,f4683])).

fof(f4667,plain,
    ( ! [X149,X148] :
        ( ~ v1_funct_2(X148,u1_struct_0(sK1),X149)
        | ~ v1_funct_1(X148)
        | v1_funct_2(k5_relat_1(sK4,X148),u1_struct_0(sK2),X149)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ r1_tarski(X148,k2_zfmisc_1(u1_struct_0(sK1),X149)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f1951,f147])).

fof(f1951,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
      | ~ v1_funct_2(X1,X4,X3)
      | ~ v1_funct_1(X1)
      | v1_funct_2(k5_relat_1(X0,X1),X2,X3)
      | ~ v1_funct_2(X0,X2,X4)
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X4)
      | ~ r1_tarski(X1,k2_zfmisc_1(X4,X3)) ) ),
    inference(resolution,[],[f115,f106])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(k5_relat_1(X3,X4),X0,X2)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X4,X1,X2)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X1) )
     => ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',fc8_funct_2)).

fof(f4678,plain,
    ( spl9_82
    | ~ spl9_17
    | ~ spl9_15
    | spl9_286
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f4666,f167,f4676,f171,f178,f493])).

fof(f4666,plain,
    ( ! [X146,X147] :
        ( ~ v1_funct_2(X146,u1_struct_0(sK2),X147)
        | ~ v1_funct_1(X146)
        | v1_funct_2(k5_relat_1(sK3,X146),u1_struct_0(sK0),X147)
        | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(u1_struct_0(sK2))
        | ~ r1_tarski(X146,k2_zfmisc_1(u1_struct_0(sK2),X147)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f1951,f168])).

fof(f4582,plain,
    ( ~ spl9_11
    | spl9_284
    | ~ spl9_6
    | ~ spl9_156 ),
    inference(avatar_split_clause,[],[f4567,f2940,f146,f4580,f157])).

fof(f4580,plain,
    ( spl9_284
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X166,sK4)))
        | ~ v1_funct_1(k5_relat_1(X166,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_284])])).

fof(f4567,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k5_relat_1(X166,sK4))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X166,sK4)))
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168)) )
    | ~ spl9_6
    | ~ spl9_156 ),
    inference(resolution,[],[f4435,f147])).

fof(f4435,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(X1,X0))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X1,X0)))
        | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_156 ),
    inference(resolution,[],[f3923,f106])).

fof(f3923,plain,
    ( ! [X182,X180,X178,X183,X181,X179] :
        ( ~ m1_subset_1(X179,k1_zfmisc_1(k2_zfmisc_1(X180,X181)))
        | ~ v1_funct_1(X178)
        | ~ v1_funct_1(X179)
        | ~ m1_subset_1(X178,k1_zfmisc_1(k2_zfmisc_1(X182,X183)))
        | ~ v1_funct_1(k5_relat_1(X179,X178))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X179,X178))) )
    | ~ spl9_156 ),
    inference(resolution,[],[f2800,f2941])).

fof(f4578,plain,
    ( ~ spl9_17
    | spl9_282
    | ~ spl9_12
    | ~ spl9_156 ),
    inference(avatar_split_clause,[],[f4566,f2940,f167,f4576,f178])).

fof(f4576,plain,
    ( spl9_282
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X163,sK3)))
        | ~ v1_funct_1(k5_relat_1(X163,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_282])])).

fof(f4566,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(k5_relat_1(X163,sK3))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(X163,sK3)))
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165)) )
    | ~ spl9_12
    | ~ spl9_156 ),
    inference(resolution,[],[f4435,f168])).

fof(f4548,plain,
    ( ~ spl9_11
    | ~ spl9_119
    | spl9_280
    | ~ spl9_6
    | ~ spl9_272 ),
    inference(avatar_split_clause,[],[f4527,f4466,f146,f4546,f1079,f157])).

fof(f4546,plain,
    ( spl9_280
  <=> v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_280])])).

fof(f4466,plain,
    ( spl9_272
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,X166)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_272])])).

fof(f4527,plain,
    ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,sK4)))
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_272 ),
    inference(resolution,[],[f4467,f147])).

fof(f4467,plain,
    ( ! [X167,X166,X168] :
        ( ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,X166)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ v1_funct_1(X166) )
    | ~ spl9_272 ),
    inference(avatar_component_clause,[],[f4466])).

fof(f4541,plain,
    ( ~ spl9_17
    | ~ spl9_115
    | spl9_278
    | ~ spl9_12
    | ~ spl9_272 ),
    inference(avatar_split_clause,[],[f4526,f4466,f167,f4539,f1037,f178])).

fof(f4539,plain,
    ( spl9_278
  <=> v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_278])])).

fof(f4526,plain,
    ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK4,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_272 ),
    inference(resolution,[],[f4467,f168])).

fof(f4508,plain,
    ( ~ spl9_11
    | ~ spl9_117
    | spl9_276
    | ~ spl9_6
    | ~ spl9_270 ),
    inference(avatar_split_clause,[],[f4487,f4462,f146,f4506,f1072,f157])).

fof(f4506,plain,
    ( spl9_276
  <=> v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_276])])).

fof(f4462,plain,
    ( spl9_270
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,X163)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_270])])).

fof(f4487,plain,
    ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,sK4)))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_270 ),
    inference(resolution,[],[f4463,f147])).

fof(f4463,plain,
    ( ! [X165,X163,X164] :
        ( ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,X163)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ v1_funct_1(X163) )
    | ~ spl9_270 ),
    inference(avatar_component_clause,[],[f4462])).

fof(f4501,plain,
    ( ~ spl9_17
    | ~ spl9_113
    | spl9_274
    | ~ spl9_12
    | ~ spl9_270 ),
    inference(avatar_split_clause,[],[f4486,f4462,f167,f4499,f1030,f178])).

fof(f4499,plain,
    ( spl9_274
  <=> v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_274])])).

fof(f4486,plain,
    ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_270 ),
    inference(resolution,[],[f4463,f168])).

fof(f4468,plain,
    ( ~ spl9_11
    | spl9_272
    | ~ spl9_6
    | ~ spl9_156 ),
    inference(avatar_split_clause,[],[f4453,f2940,f146,f4466,f157])).

fof(f4453,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,X166))) )
    | ~ spl9_6
    | ~ spl9_156 ),
    inference(resolution,[],[f3923,f147])).

fof(f4464,plain,
    ( ~ spl9_17
    | spl9_270
    | ~ spl9_12
    | ~ spl9_156 ),
    inference(avatar_split_clause,[],[f4452,f2940,f167,f4462,f178])).

fof(f4452,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,X163))) )
    | ~ spl9_12
    | ~ spl9_156 ),
    inference(resolution,[],[f3923,f168])).

fof(f4432,plain,
    ( ~ spl9_11
    | spl9_268
    | ~ spl9_6
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f4417,f2936,f146,f4430,f157])).

fof(f4430,plain,
    ( spl9_268
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X166,sK4)))
        | ~ v1_funct_1(k5_relat_1(X166,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_268])])).

fof(f4417,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k5_relat_1(X166,sK4))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X166,sK4)))
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168)) )
    | ~ spl9_6
    | ~ spl9_154 ),
    inference(resolution,[],[f4281,f147])).

fof(f4281,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(X1,X0))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X1,X0)))
        | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_154 ),
    inference(resolution,[],[f3922,f106])).

fof(f3922,plain,
    ( ! [X177,X175,X173,X176,X174,X172] :
        ( ~ m1_subset_1(X173,k1_zfmisc_1(k2_zfmisc_1(X174,X175)))
        | ~ v1_funct_1(X172)
        | ~ v1_funct_1(X173)
        | ~ m1_subset_1(X172,k1_zfmisc_1(k2_zfmisc_1(X176,X177)))
        | ~ v1_funct_1(k5_relat_1(X173,X172))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X173,X172))) )
    | ~ spl9_154 ),
    inference(resolution,[],[f2800,f2937])).

fof(f4428,plain,
    ( ~ spl9_17
    | spl9_266
    | ~ spl9_12
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f4416,f2936,f167,f4426,f178])).

fof(f4426,plain,
    ( spl9_266
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X163,sK3)))
        | ~ v1_funct_1(k5_relat_1(X163,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_266])])).

fof(f4416,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(k5_relat_1(X163,sK3))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(X163,sK3)))
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165)) )
    | ~ spl9_12
    | ~ spl9_154 ),
    inference(resolution,[],[f4281,f168])).

fof(f4398,plain,
    ( ~ spl9_11
    | ~ spl9_119
    | spl9_264
    | ~ spl9_6
    | ~ spl9_256 ),
    inference(avatar_split_clause,[],[f4377,f4312,f146,f4396,f1079,f157])).

fof(f4396,plain,
    ( spl9_264
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_264])])).

fof(f4312,plain,
    ( spl9_256
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,X166)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_256])])).

fof(f4377,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,sK4)))
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_256 ),
    inference(resolution,[],[f4313,f147])).

fof(f4313,plain,
    ( ! [X167,X166,X168] :
        ( ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,X166)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ v1_funct_1(X166) )
    | ~ spl9_256 ),
    inference(avatar_component_clause,[],[f4312])).

fof(f4391,plain,
    ( ~ spl9_17
    | ~ spl9_115
    | spl9_262
    | ~ spl9_12
    | ~ spl9_256 ),
    inference(avatar_split_clause,[],[f4376,f4312,f167,f4389,f1037,f178])).

fof(f4389,plain,
    ( spl9_262
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_262])])).

fof(f4376,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK4,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_256 ),
    inference(resolution,[],[f4313,f168])).

fof(f4354,plain,
    ( ~ spl9_11
    | ~ spl9_117
    | spl9_260
    | ~ spl9_6
    | ~ spl9_254 ),
    inference(avatar_split_clause,[],[f4333,f4308,f146,f4352,f1072,f157])).

fof(f4352,plain,
    ( spl9_260
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_260])])).

fof(f4308,plain,
    ( spl9_254
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,X163)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_254])])).

fof(f4333,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK4)))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_254 ),
    inference(resolution,[],[f4309,f147])).

fof(f4309,plain,
    ( ! [X165,X163,X164] :
        ( ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,X163)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ v1_funct_1(X163) )
    | ~ spl9_254 ),
    inference(avatar_component_clause,[],[f4308])).

fof(f4347,plain,
    ( ~ spl9_17
    | ~ spl9_113
    | spl9_258
    | ~ spl9_12
    | ~ spl9_254 ),
    inference(avatar_split_clause,[],[f4332,f4308,f167,f4345,f1030,f178])).

fof(f4345,plain,
    ( spl9_258
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_258])])).

fof(f4332,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_254 ),
    inference(resolution,[],[f4309,f168])).

fof(f4314,plain,
    ( ~ spl9_11
    | spl9_256
    | ~ spl9_6
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f4299,f2936,f146,f4312,f157])).

fof(f4299,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,X166))) )
    | ~ spl9_6
    | ~ spl9_154 ),
    inference(resolution,[],[f3922,f147])).

fof(f4310,plain,
    ( ~ spl9_17
    | spl9_254
    | ~ spl9_12
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f4298,f2936,f167,f4308,f178])).

fof(f4298,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,X163))) )
    | ~ spl9_12
    | ~ spl9_154 ),
    inference(resolution,[],[f3922,f168])).

fof(f4278,plain,
    ( ~ spl9_11
    | spl9_252
    | ~ spl9_6
    | ~ spl9_122 ),
    inference(avatar_split_clause,[],[f4263,f1168,f146,f4276,f157])).

fof(f4276,plain,
    ( spl9_252
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X166,sK4)))
        | ~ v1_funct_1(k5_relat_1(X166,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_252])])).

fof(f4263,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k5_relat_1(X166,sK4))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X166,sK4)))
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168)) )
    | ~ spl9_6
    | ~ spl9_122 ),
    inference(resolution,[],[f4131,f147])).

fof(f4131,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(X1,X0))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X1,X0)))
        | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_122 ),
    inference(resolution,[],[f3918,f106])).

fof(f3918,plain,
    ( ! [X146,X149,X147,X145,X150,X148] :
        ( ~ m1_subset_1(X146,k1_zfmisc_1(k2_zfmisc_1(X147,X148)))
        | ~ v1_funct_1(X145)
        | ~ v1_funct_1(X146)
        | ~ m1_subset_1(X145,k1_zfmisc_1(k2_zfmisc_1(X149,X150)))
        | ~ v1_funct_1(k5_relat_1(X146,X145))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X146,X145))) )
    | ~ spl9_122 ),
    inference(resolution,[],[f2800,f1169])).

fof(f4274,plain,
    ( ~ spl9_17
    | spl9_250
    | ~ spl9_12
    | ~ spl9_122 ),
    inference(avatar_split_clause,[],[f4262,f1168,f167,f4272,f178])).

fof(f4272,plain,
    ( spl9_250
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X163,sK3)))
        | ~ v1_funct_1(k5_relat_1(X163,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_250])])).

fof(f4262,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(k5_relat_1(X163,sK3))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X163,sK3)))
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165)) )
    | ~ spl9_12
    | ~ spl9_122 ),
    inference(resolution,[],[f4131,f168])).

fof(f4244,plain,
    ( ~ spl9_11
    | ~ spl9_119
    | spl9_248
    | ~ spl9_6
    | ~ spl9_240 ),
    inference(avatar_split_clause,[],[f4223,f4162,f146,f4242,f1079,f157])).

fof(f4242,plain,
    ( spl9_248
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_248])])).

fof(f4162,plain,
    ( spl9_240
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,X166)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_240])])).

fof(f4223,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,sK4)))
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_240 ),
    inference(resolution,[],[f4163,f147])).

fof(f4163,plain,
    ( ! [X167,X166,X168] :
        ( ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,X166)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ v1_funct_1(X166) )
    | ~ spl9_240 ),
    inference(avatar_component_clause,[],[f4162])).

fof(f4237,plain,
    ( ~ spl9_17
    | ~ spl9_115
    | spl9_246
    | ~ spl9_12
    | ~ spl9_240 ),
    inference(avatar_split_clause,[],[f4222,f4162,f167,f4235,f1037,f178])).

fof(f4235,plain,
    ( spl9_246
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_246])])).

fof(f4222,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK4,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_240 ),
    inference(resolution,[],[f4163,f168])).

fof(f4204,plain,
    ( ~ spl9_11
    | ~ spl9_117
    | spl9_244
    | ~ spl9_6
    | ~ spl9_238 ),
    inference(avatar_split_clause,[],[f4183,f4158,f146,f4202,f1072,f157])).

fof(f4202,plain,
    ( spl9_244
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_244])])).

fof(f4158,plain,
    ( spl9_238
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK3,X163)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_238])])).

fof(f4183,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK3,sK4)))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_238 ),
    inference(resolution,[],[f4159,f147])).

fof(f4159,plain,
    ( ! [X165,X163,X164] :
        ( ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK3,X163)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ v1_funct_1(X163) )
    | ~ spl9_238 ),
    inference(avatar_component_clause,[],[f4158])).

fof(f4197,plain,
    ( ~ spl9_17
    | ~ spl9_113
    | spl9_242
    | ~ spl9_12
    | ~ spl9_238 ),
    inference(avatar_split_clause,[],[f4182,f4158,f167,f4195,f1030,f178])).

fof(f4195,plain,
    ( spl9_242
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_242])])).

fof(f4182,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK3,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_238 ),
    inference(resolution,[],[f4159,f168])).

fof(f4164,plain,
    ( ~ spl9_11
    | spl9_240
    | ~ spl9_6
    | ~ spl9_122 ),
    inference(avatar_split_clause,[],[f4149,f1168,f146,f4162,f157])).

fof(f4149,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,X166))) )
    | ~ spl9_6
    | ~ spl9_122 ),
    inference(resolution,[],[f3918,f147])).

fof(f4160,plain,
    ( ~ spl9_17
    | spl9_238
    | ~ spl9_12
    | ~ spl9_122 ),
    inference(avatar_split_clause,[],[f4148,f1168,f167,f4158,f178])).

fof(f4148,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK3,X163))) )
    | ~ spl9_12
    | ~ spl9_122 ),
    inference(resolution,[],[f3918,f168])).

fof(f4128,plain,
    ( ~ spl9_11
    | spl9_236
    | ~ spl9_6
    | ~ spl9_120 ),
    inference(avatar_split_clause,[],[f4113,f1164,f146,f4126,f157])).

fof(f4126,plain,
    ( spl9_236
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X166,sK4)))
        | ~ v1_funct_1(k5_relat_1(X166,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_236])])).

fof(f4113,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k5_relat_1(X166,sK4))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X166,sK4)))
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168)) )
    | ~ spl9_6
    | ~ spl9_120 ),
    inference(resolution,[],[f3972,f147])).

fof(f3972,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(X1,X0))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X1,X0)))
        | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_120 ),
    inference(resolution,[],[f3917,f106])).

fof(f3917,plain,
    ( ! [X144,X142,X140,X143,X141,X139] :
        ( ~ m1_subset_1(X140,k1_zfmisc_1(k2_zfmisc_1(X141,X142)))
        | ~ v1_funct_1(X139)
        | ~ v1_funct_1(X140)
        | ~ m1_subset_1(X139,k1_zfmisc_1(k2_zfmisc_1(X143,X144)))
        | ~ v1_funct_1(k5_relat_1(X140,X139))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X140,X139))) )
    | ~ spl9_120 ),
    inference(resolution,[],[f2800,f1165])).

fof(f4124,plain,
    ( ~ spl9_17
    | spl9_234
    | ~ spl9_12
    | ~ spl9_120 ),
    inference(avatar_split_clause,[],[f4112,f1164,f167,f4122,f178])).

fof(f4122,plain,
    ( spl9_234
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X163,sK3)))
        | ~ v1_funct_1(k5_relat_1(X163,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_234])])).

fof(f4112,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(k5_relat_1(X163,sK3))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(X163,sK3)))
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165)) )
    | ~ spl9_12
    | ~ spl9_120 ),
    inference(resolution,[],[f3972,f168])).

fof(f4094,plain,
    ( ~ spl9_11
    | ~ spl9_119
    | spl9_232
    | ~ spl9_6
    | ~ spl9_224 ),
    inference(avatar_split_clause,[],[f4073,f4003,f146,f4092,f1079,f157])).

fof(f4092,plain,
    ( spl9_232
  <=> v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_232])])).

fof(f4003,plain,
    ( spl9_224
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK4,X166)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_224])])).

fof(f4073,plain,
    ( v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK4,sK4)))
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_224 ),
    inference(resolution,[],[f4004,f147])).

fof(f4004,plain,
    ( ! [X167,X166,X168] :
        ( ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK4,X166)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ v1_funct_1(X166) )
    | ~ spl9_224 ),
    inference(avatar_component_clause,[],[f4003])).

fof(f4087,plain,
    ( ~ spl9_17
    | ~ spl9_115
    | spl9_230
    | ~ spl9_12
    | ~ spl9_224 ),
    inference(avatar_split_clause,[],[f4072,f4003,f167,f4085,f1037,f178])).

fof(f4085,plain,
    ( spl9_230
  <=> v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_230])])).

fof(f4072,plain,
    ( v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK4,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK4,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_224 ),
    inference(resolution,[],[f4004,f168])).

fof(f4045,plain,
    ( ~ spl9_11
    | ~ spl9_117
    | spl9_228
    | ~ spl9_6
    | ~ spl9_222 ),
    inference(avatar_split_clause,[],[f4024,f3999,f146,f4043,f1072,f157])).

fof(f4043,plain,
    ( spl9_228
  <=> v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_228])])).

fof(f3999,plain,
    ( spl9_222
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK3,X163)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_222])])).

fof(f4024,plain,
    ( v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK3,sK4)))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_222 ),
    inference(resolution,[],[f4000,f147])).

fof(f4000,plain,
    ( ! [X165,X163,X164] :
        ( ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK3,X163)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ v1_funct_1(X163) )
    | ~ spl9_222 ),
    inference(avatar_component_clause,[],[f3999])).

fof(f4038,plain,
    ( ~ spl9_17
    | ~ spl9_113
    | spl9_226
    | ~ spl9_12
    | ~ spl9_222 ),
    inference(avatar_split_clause,[],[f4023,f3999,f167,f4036,f1030,f178])).

fof(f4036,plain,
    ( spl9_226
  <=> v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_226])])).

fof(f4023,plain,
    ( v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)))
    | ~ v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_222 ),
    inference(resolution,[],[f4000,f168])).

fof(f4005,plain,
    ( ~ spl9_11
    | spl9_224
    | ~ spl9_6
    | ~ spl9_120 ),
    inference(avatar_split_clause,[],[f3990,f1164,f146,f4003,f157])).

fof(f3990,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK4,X166))) )
    | ~ spl9_6
    | ~ spl9_120 ),
    inference(resolution,[],[f3917,f147])).

fof(f4001,plain,
    ( ~ spl9_17
    | spl9_222
    | ~ spl9_12
    | ~ spl9_120 ),
    inference(avatar_split_clause,[],[f3989,f1164,f167,f3999,f178])).

fof(f3989,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | v1_funct_1(k5_relat_1(sK3,k5_relat_1(sK3,X163))) )
    | ~ spl9_12
    | ~ spl9_120 ),
    inference(resolution,[],[f3917,f168])).

fof(f3736,plain,
    ( ~ spl9_11
    | spl9_220
    | ~ spl9_6
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f3721,f2703,f146,f3734,f157])).

fof(f3734,plain,
    ( spl9_220
  <=> ! [X168,X166,X167] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(sK4,X166),sK4))
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ v1_funct_1(X166) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_220])])).

fof(f3721,plain,
    ( ! [X167,X166,X168] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(sK4,X166),sK4))
        | ~ v1_funct_1(X166)
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ v1_funct_1(sK4)
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168)) )
    | ~ spl9_6
    | ~ spl9_144 ),
    inference(resolution,[],[f3589,f147])).

fof(f3589,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_relat_1(k5_relat_1(k5_relat_1(X0,X1),sK4))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(k5_relat_1(X0,X1))
        | ~ v1_funct_1(X0)
        | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_144 ),
    inference(resolution,[],[f2805,f106])).

fof(f2805,plain,
    ( ! [X14,X19,X17,X15,X18,X16] :
        ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_funct_1(k5_relat_1(X14,X15))
        | v1_relat_1(k5_relat_1(k5_relat_1(X14,X15),sK4))
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ v1_funct_1(X14) )
    | ~ spl9_144 ),
    inference(resolution,[],[f2704,f833])).

fof(f3732,plain,
    ( ~ spl9_17
    | spl9_218
    | ~ spl9_12
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f3720,f2703,f167,f3730,f178])).

fof(f3730,plain,
    ( spl9_218
  <=> ! [X164,X163,X165] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,X163),sK4))
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ v1_funct_1(X163) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_218])])).

fof(f3720,plain,
    ( ! [X165,X163,X164] :
        ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,X163),sK4))
        | ~ v1_funct_1(X163)
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165)) )
    | ~ spl9_12
    | ~ spl9_144 ),
    inference(resolution,[],[f3589,f168])).

fof(f3702,plain,
    ( spl9_216
    | ~ spl9_119
    | ~ spl9_11
    | ~ spl9_6
    | ~ spl9_208 ),
    inference(avatar_split_clause,[],[f3681,f3620,f146,f157,f1079,f3700])).

fof(f3700,plain,
    ( spl9_216
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_216])])).

fof(f3620,plain,
    ( spl9_208
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(k5_relat_1(X166,sK4))
        | ~ v1_funct_1(X166)
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | v1_relat_1(k5_relat_1(k5_relat_1(X166,sK4),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_208])])).

fof(f3681,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK4),sK4))
    | ~ spl9_6
    | ~ spl9_208 ),
    inference(resolution,[],[f3621,f147])).

fof(f3621,plain,
    ( ! [X167,X166,X168] :
        ( ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | ~ v1_funct_1(X166)
        | ~ v1_funct_1(k5_relat_1(X166,sK4))
        | v1_relat_1(k5_relat_1(k5_relat_1(X166,sK4),sK4)) )
    | ~ spl9_208 ),
    inference(avatar_component_clause,[],[f3620])).

fof(f3695,plain,
    ( spl9_214
    | ~ spl9_117
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_208 ),
    inference(avatar_split_clause,[],[f3680,f3620,f167,f178,f1072,f3693])).

fof(f3693,plain,
    ( spl9_214
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_214])])).

fof(f3680,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),sK4))
    | ~ spl9_12
    | ~ spl9_208 ),
    inference(resolution,[],[f3621,f168])).

fof(f3662,plain,
    ( spl9_212
    | ~ spl9_115
    | ~ spl9_11
    | ~ spl9_6
    | ~ spl9_206 ),
    inference(avatar_split_clause,[],[f3641,f3616,f146,f157,f1037,f3660])).

fof(f3660,plain,
    ( spl9_212
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_212])])).

fof(f3616,plain,
    ( spl9_206
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(k5_relat_1(X163,sK3))
        | ~ v1_funct_1(X163)
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | v1_relat_1(k5_relat_1(k5_relat_1(X163,sK3),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_206])])).

fof(f3641,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_1(k5_relat_1(sK4,sK3))
    | v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK3),sK4))
    | ~ spl9_6
    | ~ spl9_206 ),
    inference(resolution,[],[f3617,f147])).

fof(f3617,plain,
    ( ! [X165,X163,X164] :
        ( ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | ~ v1_funct_1(X163)
        | ~ v1_funct_1(k5_relat_1(X163,sK3))
        | v1_relat_1(k5_relat_1(k5_relat_1(X163,sK3),sK4)) )
    | ~ spl9_206 ),
    inference(avatar_component_clause,[],[f3616])).

fof(f3655,plain,
    ( spl9_210
    | ~ spl9_113
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_206 ),
    inference(avatar_split_clause,[],[f3640,f3616,f167,f178,f1030,f3653])).

fof(f3653,plain,
    ( spl9_210
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_210])])).

fof(f3640,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_1(k5_relat_1(sK3,sK3))
    | v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK4))
    | ~ spl9_12
    | ~ spl9_206 ),
    inference(resolution,[],[f3617,f168])).

fof(f3622,plain,
    ( ~ spl9_11
    | spl9_208
    | ~ spl9_6
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f3607,f2703,f146,f3620,f157])).

fof(f3607,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(k5_relat_1(X166,sK4))
        | v1_relat_1(k5_relat_1(k5_relat_1(X166,sK4),sK4))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | ~ v1_funct_1(X166) )
    | ~ spl9_6
    | ~ spl9_144 ),
    inference(resolution,[],[f2805,f147])).

fof(f3618,plain,
    ( ~ spl9_17
    | spl9_206
    | ~ spl9_12
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f3606,f2703,f167,f3616,f178])).

fof(f3606,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(k5_relat_1(X163,sK3))
        | v1_relat_1(k5_relat_1(k5_relat_1(X163,sK3),sK4))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | ~ v1_funct_1(X163) )
    | ~ spl9_12
    | ~ spl9_144 ),
    inference(resolution,[],[f2805,f168])).

fof(f3559,plain,
    ( spl9_204
    | ~ spl9_11
    | ~ spl9_6
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f3544,f2699,f146,f157,f3557])).

fof(f3557,plain,
    ( spl9_204
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168))
        | ~ v1_funct_1(k5_relat_1(X166,sK4))
        | v1_relat_1(k5_relat_1(k5_relat_1(X166,sK4),sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_204])])).

fof(f3544,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_1(X166)
        | v1_relat_1(k5_relat_1(k5_relat_1(X166,sK4),sK3))
        | ~ v1_funct_1(k5_relat_1(X166,sK4))
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168)) )
    | ~ spl9_6
    | ~ spl9_142 ),
    inference(resolution,[],[f3403,f147])).

fof(f3403,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(X3)
        | v1_relat_1(k5_relat_1(k5_relat_1(X3,X0),sK3))
        | ~ v1_funct_1(k5_relat_1(X3,X0))
        | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_142 ),
    inference(resolution,[],[f2778,f106])).

fof(f2778,plain,
    ( ! [X134,X138,X136,X135,X133,X137] :
        ( ~ m1_subset_1(X136,k1_zfmisc_1(k2_zfmisc_1(X137,X138)))
        | ~ v1_funct_1(X133)
        | ~ m1_subset_1(X133,k1_zfmisc_1(k2_zfmisc_1(X134,X135)))
        | ~ v1_funct_1(X136)
        | v1_relat_1(k5_relat_1(k5_relat_1(X136,X133),sK3))
        | ~ v1_funct_1(k5_relat_1(X136,X133)) )
    | ~ spl9_142 ),
    inference(resolution,[],[f833,f2700])).

fof(f3555,plain,
    ( spl9_202
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f3543,f2699,f167,f178,f3553])).

fof(f3553,plain,
    ( spl9_202
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165))
        | ~ v1_funct_1(k5_relat_1(X163,sK3))
        | v1_relat_1(k5_relat_1(k5_relat_1(X163,sK3),sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_202])])).

fof(f3543,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X163)
        | v1_relat_1(k5_relat_1(k5_relat_1(X163,sK3),sK3))
        | ~ v1_funct_1(k5_relat_1(X163,sK3))
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165)) )
    | ~ spl9_12
    | ~ spl9_142 ),
    inference(resolution,[],[f3403,f168])).

fof(f3525,plain,
    ( ~ spl9_11
    | spl9_200
    | ~ spl9_119
    | ~ spl9_6
    | ~ spl9_192 ),
    inference(avatar_split_clause,[],[f3504,f3434,f146,f1079,f3523,f157])).

fof(f3523,plain,
    ( spl9_200
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_200])])).

fof(f3434,plain,
    ( spl9_192
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | v1_relat_1(k5_relat_1(k5_relat_1(sK4,X166),sK3))
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_192])])).

fof(f3504,plain,
    ( ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK4),sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_192 ),
    inference(resolution,[],[f3435,f147])).

fof(f3435,plain,
    ( ! [X167,X166,X168] :
        ( ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | v1_relat_1(k5_relat_1(k5_relat_1(sK4,X166),sK3))
        | ~ v1_funct_1(X166) )
    | ~ spl9_192 ),
    inference(avatar_component_clause,[],[f3434])).

fof(f3518,plain,
    ( ~ spl9_17
    | spl9_198
    | ~ spl9_115
    | ~ spl9_12
    | ~ spl9_192 ),
    inference(avatar_split_clause,[],[f3503,f3434,f167,f1037,f3516,f178])).

fof(f3516,plain,
    ( spl9_198
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_198])])).

fof(f3503,plain,
    ( ~ v1_funct_1(k5_relat_1(sK4,sK3))
    | v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK3),sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_192 ),
    inference(resolution,[],[f3435,f168])).

fof(f3485,plain,
    ( ~ spl9_11
    | spl9_196
    | ~ spl9_117
    | ~ spl9_6
    | ~ spl9_190 ),
    inference(avatar_split_clause,[],[f3464,f3430,f146,f1072,f3483,f157])).

fof(f3483,plain,
    ( spl9_196
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_196])])).

fof(f3430,plain,
    ( spl9_190
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | v1_relat_1(k5_relat_1(k5_relat_1(sK3,X163),sK3))
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_190])])).

fof(f3464,plain,
    ( ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_190 ),
    inference(resolution,[],[f3431,f147])).

fof(f3431,plain,
    ( ! [X165,X163,X164] :
        ( ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | v1_relat_1(k5_relat_1(k5_relat_1(sK3,X163),sK3))
        | ~ v1_funct_1(X163) )
    | ~ spl9_190 ),
    inference(avatar_component_clause,[],[f3430])).

fof(f3478,plain,
    ( ~ spl9_17
    | spl9_194
    | ~ spl9_113
    | ~ spl9_12
    | ~ spl9_190 ),
    inference(avatar_split_clause,[],[f3463,f3430,f167,f1030,f3476,f178])).

fof(f3476,plain,
    ( spl9_194
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_194])])).

fof(f3463,plain,
    ( ~ v1_funct_1(k5_relat_1(sK3,sK3))
    | v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_190 ),
    inference(resolution,[],[f3431,f168])).

fof(f3436,plain,
    ( ~ spl9_11
    | spl9_192
    | ~ spl9_6
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f3421,f2699,f146,f3434,f157])).

fof(f3421,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | ~ v1_funct_1(sK4)
        | v1_relat_1(k5_relat_1(k5_relat_1(sK4,X166),sK3))
        | ~ v1_funct_1(k5_relat_1(sK4,X166)) )
    | ~ spl9_6
    | ~ spl9_142 ),
    inference(resolution,[],[f2778,f147])).

fof(f3432,plain,
    ( ~ spl9_17
    | spl9_190
    | ~ spl9_12
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f3420,f2699,f167,f3430,f178])).

fof(f3420,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | ~ v1_funct_1(sK3)
        | v1_relat_1(k5_relat_1(k5_relat_1(sK3,X163),sK3))
        | ~ v1_funct_1(k5_relat_1(sK3,X163)) )
    | ~ spl9_12
    | ~ spl9_142 ),
    inference(resolution,[],[f2778,f168])).

fof(f3373,plain,
    ( spl9_188
    | ~ spl9_11
    | ~ spl9_6
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f3358,f1008,f146,f157,f3371])).

fof(f3371,plain,
    ( spl9_188
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168))
        | v1_funct_1(k5_relat_1(k5_relat_1(X166,sK4),sK4))
        | ~ v1_funct_1(k5_relat_1(X166,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_188])])).

fof(f3358,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_1(X166)
        | ~ v1_funct_1(k5_relat_1(X166,sK4))
        | v1_funct_1(k5_relat_1(k5_relat_1(X166,sK4),sK4))
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168)) )
    | ~ spl9_6
    | ~ spl9_110 ),
    inference(resolution,[],[f3226,f147])).

fof(f3226,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(k5_relat_1(X3,X0))
        | v1_funct_1(k5_relat_1(k5_relat_1(X3,X0),sK4))
        | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_110 ),
    inference(resolution,[],[f2773,f106])).

fof(f2773,plain,
    ( ! [X101,X99,X97,X102,X100,X98] :
        ( ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(X101,X102)))
        | ~ v1_funct_1(X97)
        | ~ m1_subset_1(X97,k1_zfmisc_1(k2_zfmisc_1(X98,X99)))
        | ~ v1_funct_1(X100)
        | ~ v1_funct_1(k5_relat_1(X100,X97))
        | v1_funct_1(k5_relat_1(k5_relat_1(X100,X97),sK4)) )
    | ~ spl9_110 ),
    inference(resolution,[],[f833,f1009])).

fof(f3369,plain,
    ( spl9_186
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f3357,f1008,f167,f178,f3367])).

fof(f3367,plain,
    ( spl9_186
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165))
        | v1_funct_1(k5_relat_1(k5_relat_1(X163,sK3),sK4))
        | ~ v1_funct_1(k5_relat_1(X163,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_186])])).

fof(f3357,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X163)
        | ~ v1_funct_1(k5_relat_1(X163,sK3))
        | v1_funct_1(k5_relat_1(k5_relat_1(X163,sK3),sK4))
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165)) )
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(resolution,[],[f3226,f168])).

fof(f3339,plain,
    ( ~ spl9_11
    | ~ spl9_119
    | spl9_184
    | ~ spl9_6
    | ~ spl9_176 ),
    inference(avatar_split_clause,[],[f3318,f3257,f146,f3337,f1079,f157])).

fof(f3337,plain,
    ( spl9_184
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_184])])).

fof(f3257,plain,
    ( spl9_176
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | v1_funct_1(k5_relat_1(k5_relat_1(sK4,X166),sK4))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_176])])).

fof(f3318,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK4),sK4))
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_176 ),
    inference(resolution,[],[f3258,f147])).

fof(f3258,plain,
    ( ! [X167,X166,X168] :
        ( ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK4,X166),sK4))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ v1_funct_1(X166) )
    | ~ spl9_176 ),
    inference(avatar_component_clause,[],[f3257])).

fof(f3332,plain,
    ( ~ spl9_17
    | ~ spl9_115
    | spl9_182
    | ~ spl9_12
    | ~ spl9_176 ),
    inference(avatar_split_clause,[],[f3317,f3257,f167,f3330,f1037,f178])).

fof(f3330,plain,
    ( spl9_182
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_182])])).

fof(f3317,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK3),sK4))
    | ~ v1_funct_1(k5_relat_1(sK4,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_176 ),
    inference(resolution,[],[f3258,f168])).

fof(f3299,plain,
    ( ~ spl9_11
    | ~ spl9_117
    | spl9_180
    | ~ spl9_6
    | ~ spl9_174 ),
    inference(avatar_split_clause,[],[f3278,f3253,f146,f3297,f1072,f157])).

fof(f3297,plain,
    ( spl9_180
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK3,sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_180])])).

fof(f3253,plain,
    ( spl9_174
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | v1_funct_1(k5_relat_1(k5_relat_1(sK3,X163),sK4))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_174])])).

fof(f3278,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK3,sK4),sK4))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_174 ),
    inference(resolution,[],[f3254,f147])).

fof(f3254,plain,
    ( ! [X165,X163,X164] :
        ( ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK3,X163),sK4))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ v1_funct_1(X163) )
    | ~ spl9_174 ),
    inference(avatar_component_clause,[],[f3253])).

fof(f3292,plain,
    ( ~ spl9_17
    | ~ spl9_113
    | spl9_178
    | ~ spl9_12
    | ~ spl9_174 ),
    inference(avatar_split_clause,[],[f3277,f3253,f167,f3290,f1030,f178])).

fof(f3290,plain,
    ( spl9_178
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK3,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_178])])).

fof(f3277,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK3,sK3),sK4))
    | ~ v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_174 ),
    inference(resolution,[],[f3254,f168])).

fof(f3259,plain,
    ( ~ spl9_11
    | spl9_176
    | ~ spl9_6
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f3244,f1008,f146,f3257,f157])).

fof(f3244,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK4,X166),sK4)) )
    | ~ spl9_6
    | ~ spl9_110 ),
    inference(resolution,[],[f2773,f147])).

fof(f3255,plain,
    ( ~ spl9_17
    | spl9_174
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f3243,f1008,f167,f3253,f178])).

fof(f3243,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK3,X163),sK4)) )
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(resolution,[],[f2773,f168])).

fof(f3223,plain,
    ( spl9_172
    | ~ spl9_11
    | ~ spl9_6
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f3208,f1004,f146,f157,f3221])).

fof(f3221,plain,
    ( spl9_172
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168))
        | v1_funct_1(k5_relat_1(k5_relat_1(X166,sK4),sK3))
        | ~ v1_funct_1(k5_relat_1(X166,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_172])])).

fof(f3208,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_1(X166)
        | ~ v1_funct_1(k5_relat_1(X166,sK4))
        | v1_funct_1(k5_relat_1(k5_relat_1(X166,sK4),sK3))
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168)) )
    | ~ spl9_6
    | ~ spl9_108 ),
    inference(resolution,[],[f3014,f147])).

fof(f3014,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(k5_relat_1(X3,X0))
        | v1_funct_1(k5_relat_1(k5_relat_1(X3,X0),sK3))
        | ~ r1_tarski(X3,k2_zfmisc_1(X4,X5)) )
    | ~ spl9_108 ),
    inference(resolution,[],[f2772,f106])).

fof(f2772,plain,
    ( ! [X94,X92,X95,X93,X91,X96] :
        ( ~ m1_subset_1(X94,k1_zfmisc_1(k2_zfmisc_1(X95,X96)))
        | ~ v1_funct_1(X91)
        | ~ m1_subset_1(X91,k1_zfmisc_1(k2_zfmisc_1(X92,X93)))
        | ~ v1_funct_1(X94)
        | ~ v1_funct_1(k5_relat_1(X94,X91))
        | v1_funct_1(k5_relat_1(k5_relat_1(X94,X91),sK3)) )
    | ~ spl9_108 ),
    inference(resolution,[],[f833,f1005])).

fof(f3219,plain,
    ( spl9_170
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f3207,f1004,f167,f178,f3217])).

fof(f3217,plain,
    ( spl9_170
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165))
        | v1_funct_1(k5_relat_1(k5_relat_1(X163,sK3),sK3))
        | ~ v1_funct_1(k5_relat_1(X163,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_170])])).

fof(f3207,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X163)
        | ~ v1_funct_1(k5_relat_1(X163,sK3))
        | v1_funct_1(k5_relat_1(k5_relat_1(X163,sK3),sK3))
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165)) )
    | ~ spl9_12
    | ~ spl9_108 ),
    inference(resolution,[],[f3014,f168])).

fof(f3127,plain,
    ( ~ spl9_11
    | ~ spl9_119
    | spl9_168
    | ~ spl9_6
    | ~ spl9_160 ),
    inference(avatar_split_clause,[],[f3106,f3045,f146,f3125,f1079,f157])).

fof(f3125,plain,
    ( spl9_168
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_168])])).

fof(f3045,plain,
    ( spl9_160
  <=> ! [X168,X166,X167] :
        ( ~ v1_funct_1(X166)
        | v1_funct_1(k5_relat_1(k5_relat_1(sK4,X166),sK3))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_160])])).

fof(f3106,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK4),sK3))
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_160 ),
    inference(resolution,[],[f3046,f147])).

fof(f3046,plain,
    ( ! [X167,X166,X168] :
        ( ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK4,X166),sK3))
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | ~ v1_funct_1(X166) )
    | ~ spl9_160 ),
    inference(avatar_component_clause,[],[f3045])).

fof(f3120,plain,
    ( ~ spl9_17
    | ~ spl9_115
    | spl9_166
    | ~ spl9_12
    | ~ spl9_160 ),
    inference(avatar_split_clause,[],[f3105,f3045,f167,f3118,f1037,f178])).

fof(f3118,plain,
    ( spl9_166
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_166])])).

fof(f3105,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK3),sK3))
    | ~ v1_funct_1(k5_relat_1(sK4,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_160 ),
    inference(resolution,[],[f3046,f168])).

fof(f3087,plain,
    ( ~ spl9_11
    | ~ spl9_117
    | spl9_164
    | ~ spl9_6
    | ~ spl9_158 ),
    inference(avatar_split_clause,[],[f3066,f3041,f146,f3085,f1072,f157])).

fof(f3085,plain,
    ( spl9_164
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK3,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_164])])).

fof(f3041,plain,
    ( spl9_158
  <=> ! [X164,X163,X165] :
        ( ~ v1_funct_1(X163)
        | v1_funct_1(k5_relat_1(k5_relat_1(sK3,X163),sK3))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).

fof(f3066,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK3,sK4),sK3))
    | ~ v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_158 ),
    inference(resolution,[],[f3042,f147])).

fof(f3042,plain,
    ( ! [X165,X163,X164] :
        ( ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK3,X163),sK3))
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | ~ v1_funct_1(X163) )
    | ~ spl9_158 ),
    inference(avatar_component_clause,[],[f3041])).

fof(f3080,plain,
    ( ~ spl9_17
    | ~ spl9_113
    | spl9_162
    | ~ spl9_12
    | ~ spl9_158 ),
    inference(avatar_split_clause,[],[f3065,f3041,f167,f3078,f1030,f178])).

fof(f3078,plain,
    ( spl9_162
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK3,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_162])])).

fof(f3065,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK3,sK3),sK3))
    | ~ v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_158 ),
    inference(resolution,[],[f3042,f168])).

fof(f3047,plain,
    ( ~ spl9_11
    | spl9_160
    | ~ spl9_6
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f3032,f1004,f146,f3045,f157])).

fof(f3032,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ m1_subset_1(X166,k1_zfmisc_1(k2_zfmisc_1(X167,X168)))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k5_relat_1(sK4,X166))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK4,X166),sK3)) )
    | ~ spl9_6
    | ~ spl9_108 ),
    inference(resolution,[],[f2772,f147])).

fof(f3043,plain,
    ( ~ spl9_17
    | spl9_158
    | ~ spl9_12
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f3031,f1004,f167,f3041,f178])).

fof(f3031,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ m1_subset_1(X163,k1_zfmisc_1(k2_zfmisc_1(X164,X165)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(k5_relat_1(sK3,X163))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK3,X163),sK3)) )
    | ~ spl9_12
    | ~ spl9_108 ),
    inference(resolution,[],[f2772,f168])).

fof(f2942,plain,
    ( ~ spl9_11
    | spl9_156
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f2927,f146,f2940,f157])).

fof(f2927,plain,
    ( ! [X167,X166,X168] :
        ( ~ v1_funct_1(X166)
        | ~ v1_funct_1(sK4)
        | v1_relat_1(k5_relat_1(sK4,X166))
        | ~ r1_tarski(X166,k2_zfmisc_1(X167,X168)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f2673,f147])).

fof(f2938,plain,
    ( ~ spl9_17
    | spl9_154
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f2926,f167,f2936,f178])).

fof(f2926,plain,
    ( ! [X165,X163,X164] :
        ( ~ v1_funct_1(X163)
        | ~ v1_funct_1(sK3)
        | v1_relat_1(k5_relat_1(sK3,X163))
        | ~ r1_tarski(X163,k2_zfmisc_1(X164,X165)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f2673,f168])).

fof(f2841,plain,
    ( ~ spl9_11
    | spl9_152
    | ~ spl9_6
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f2820,f2703,f146,f2839,f157])).

fof(f2839,plain,
    ( spl9_152
  <=> v1_relat_1(k5_relat_1(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_152])])).

fof(f2820,plain,
    ( v1_relat_1(k5_relat_1(sK4,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_144 ),
    inference(resolution,[],[f2704,f147])).

fof(f2834,plain,
    ( ~ spl9_17
    | spl9_150
    | ~ spl9_12
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f2819,f2703,f167,f2832,f178])).

fof(f2832,plain,
    ( spl9_150
  <=> v1_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_150])])).

fof(f2819,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_144 ),
    inference(resolution,[],[f2704,f168])).

fof(f2744,plain,
    ( ~ spl9_11
    | spl9_148
    | ~ spl9_6
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f2723,f2699,f146,f2742,f157])).

fof(f2742,plain,
    ( spl9_148
  <=> v1_relat_1(k5_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_148])])).

fof(f2723,plain,
    ( v1_relat_1(k5_relat_1(sK4,sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl9_6
    | ~ spl9_142 ),
    inference(resolution,[],[f2700,f147])).

fof(f2737,plain,
    ( ~ spl9_17
    | spl9_146
    | ~ spl9_12
    | ~ spl9_142 ),
    inference(avatar_split_clause,[],[f2722,f2699,f167,f2735,f178])).

fof(f2735,plain,
    ( spl9_146
  <=> v1_relat_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_146])])).

fof(f2722,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl9_12
    | ~ spl9_142 ),
    inference(resolution,[],[f2700,f168])).

fof(f2705,plain,
    ( spl9_144
    | ~ spl9_11
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f2690,f146,f157,f2703])).

fof(f2690,plain,
    ( ! [X158,X159,X157] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X157,k1_zfmisc_1(k2_zfmisc_1(X158,X159)))
        | ~ v1_funct_1(X157)
        | v1_relat_1(k5_relat_1(X157,sK4)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f2672,f147])).

fof(f2701,plain,
    ( spl9_142
    | ~ spl9_17
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f2689,f167,f178,f2699])).

fof(f2689,plain,
    ( ! [X156,X154,X155] :
        ( ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X154,k1_zfmisc_1(k2_zfmisc_1(X155,X156)))
        | ~ v1_funct_1(X154)
        | v1_relat_1(k5_relat_1(X154,sK3)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f2672,f168])).

fof(f2641,plain,
    ( spl9_82
    | spl9_140
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f2637,f146,f2639,f493])).

fof(f2639,plain,
    ( spl9_140
  <=> ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK4,X0))
        | r2_hidden(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK4,X0)))))),u1_struct_0(sK2))
        | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK4,X0))))))
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK4,X0))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_140])])).

fof(f2637,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK4,X0))
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK4,X0)))))
        | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK4,X0))))))
        | v1_xboole_0(u1_struct_0(sK2))
        | r2_hidden(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK4,X0)))))),u1_struct_0(sK2)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f1688,f103])).

fof(f1688,plain,
    ( ! [X12] :
        ( m1_subset_1(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK4,X12)))))),u1_struct_0(sK2))
        | v1_xboole_0(k10_relat_1(sK4,X12))
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK4,X12)))))
        | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k10_relat_1(sK4,X12)))))) )
    | ~ spl9_6 ),
    inference(resolution,[],[f959,f490])).

fof(f2632,plain,
    ( spl9_82
    | spl9_138
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f2628,f146,f2630,f493])).

fof(f2630,plain,
    ( spl9_138
  <=> ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK4,X0))
        | r2_hidden(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK4,X0)))))),u1_struct_0(sK2))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK4,X0))))
        | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK4,X0)))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_138])])).

fof(f2628,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK4,X0))
        | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK4,X0))))))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK4,X0))))
        | v1_xboole_0(u1_struct_0(sK2))
        | r2_hidden(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK4,X0)))))),u1_struct_0(sK2)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f1304,f103])).

fof(f1304,plain,
    ( ! [X12] :
        ( m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK4,X12)))))),u1_struct_0(sK2))
        | v1_xboole_0(k10_relat_1(sK4,X12))
        | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k10_relat_1(sK4,X12))))))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK4,X12)))) )
    | ~ spl9_6 ),
    inference(resolution,[],[f846,f490])).

fof(f2135,plain,
    ( spl9_82
    | spl9_136
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f2124,f146,f2133,f493])).

fof(f2133,plain,
    ( spl9_136
  <=> ! [X91] :
        ( v1_xboole_0(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X91))
        | r2_hidden(sK6(k10_relat_1(sK4,X91)),u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f2124,plain,
    ( ! [X91] :
        ( v1_xboole_0(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X91))
        | v1_xboole_0(u1_struct_0(sK2))
        | r2_hidden(sK6(k10_relat_1(sK4,X91)),u1_struct_0(sK2)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f2109,f147])).

fof(f2056,plain,
    ( spl9_82
    | spl9_134
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f2052,f146,f2054,f493])).

fof(f2054,plain,
    ( spl9_134
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK4,X0),X1))),X2))
        | r2_hidden(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK4,X0),X1))),X2)),u1_struct_0(sK2))
        | v1_xboole_0(k10_relat_1(sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f2052,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK4,X0),X1))),X2))
        | v1_xboole_0(k10_relat_1(sK4,X0))
        | v1_xboole_0(u1_struct_0(sK2))
        | r2_hidden(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK4,X0),X1))),X2)),u1_struct_0(sK2)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f1404,f103])).

fof(f1404,plain,
    ( ! [X26,X24,X25] :
        ( m1_subset_1(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK4,X24),X25))),X26)),u1_struct_0(sK2))
        | v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK4,X24),X25))),X26))
        | v1_xboole_0(k10_relat_1(sK4,X24)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f883,f490])).

fof(f2043,plain,
    ( spl9_78
    | spl9_132
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f2039,f167,f2041,f481])).

fof(f2041,plain,
    ( spl9_132
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X0),X1))),X2))
        | r2_hidden(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X0),X1))),X2)),u1_struct_0(sK0))
        | v1_xboole_0(k10_relat_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_132])])).

fof(f2039,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X0),X1))),X2))
        | v1_xboole_0(k10_relat_1(sK3,X0))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X0),X1))),X2)),u1_struct_0(sK0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f1403,f103])).

fof(f1403,plain,
    ( ! [X23,X21,X22] :
        ( m1_subset_1(sK6(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X21),X22))),X23)),u1_struct_0(sK0))
        | v1_xboole_0(k10_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK3,X21),X22))),X23))
        | v1_xboole_0(k10_relat_1(sK3,X21)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f883,f478])).

fof(f2038,plain,
    ( spl9_130
    | ~ spl9_15
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f2024,f1978,f167,f178,f171,f2036])).

fof(f2024,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    | v1_funct_2(k5_relat_1(sK3,sK4),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_12
    | ~ spl9_126 ),
    inference(resolution,[],[f1979,f168])).

fof(f1984,plain,
    ( spl9_128
    | ~ spl9_79
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f785,f273,f484,f1982])).

fof(f1982,plain,
    ( spl9_128
  <=> ! [X18] : v1_xboole_0(k10_relat_1(sK3,X18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).

fof(f785,plain,
    ( ! [X18] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k10_relat_1(sK3,X18)) )
    | ~ spl9_40 ),
    inference(resolution,[],[f781,f274])).

fof(f1980,plain,
    ( spl9_82
    | ~ spl9_11
    | ~ spl9_9
    | spl9_126
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f1965,f146,f1978,f150,f157,f493])).

fof(f1965,plain,
    ( ! [X105,X106] :
        ( v1_funct_2(k5_relat_1(X105,sK4),X106,u1_struct_0(sK1))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X105,k1_zfmisc_1(k2_zfmisc_1(X106,u1_struct_0(sK2))))
        | ~ v1_funct_2(X105,X106,u1_struct_0(sK2))
        | ~ v1_funct_1(X105)
        | v1_xboole_0(u1_struct_0(sK2)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f115,f147])).

fof(f1976,plain,
    ( spl9_78
    | ~ spl9_17
    | ~ spl9_15
    | spl9_124
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f1964,f167,f1974,f171,f178,f481])).

fof(f1974,plain,
    ( spl9_124
  <=> ! [X104,X103] :
        ( v1_funct_2(k5_relat_1(X103,sK3),X104,u1_struct_0(sK2))
        | ~ v1_funct_1(X103)
        | ~ v1_funct_2(X103,X104,u1_struct_0(sK0))
        | ~ m1_subset_1(X103,k1_zfmisc_1(k2_zfmisc_1(X104,u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f1964,plain,
    ( ! [X103,X104] :
        ( v1_funct_2(k5_relat_1(X103,sK3),X104,u1_struct_0(sK2))
        | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X103,k1_zfmisc_1(k2_zfmisc_1(X104,u1_struct_0(sK0))))
        | ~ v1_funct_2(X103,X104,u1_struct_0(sK0))
        | ~ v1_funct_1(X103)
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f115,f168])).

fof(f1170,plain,
    ( ~ spl9_11
    | spl9_122
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f1157,f146,f1168,f157])).

fof(f1157,plain,
    ( ! [X101,X99,X100] :
        ( ~ v1_funct_1(X99)
        | v1_funct_1(k5_relat_1(sK4,X99))
        | ~ v1_funct_1(sK4)
        | ~ r1_tarski(X99,k2_zfmisc_1(X100,X101)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f985,f147])).

fof(f1166,plain,
    ( ~ spl9_17
    | spl9_120
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f1156,f167,f1164,f178])).

fof(f1156,plain,
    ( ! [X97,X98,X96] :
        ( ~ v1_funct_1(X96)
        | v1_funct_1(k5_relat_1(sK3,X96))
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(X96,k2_zfmisc_1(X97,X98)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f985,f168])).

fof(f1084,plain,
    ( spl9_118
    | ~ spl9_11
    | ~ spl9_6
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f1065,f1008,f146,f157,f1082])).

fof(f1082,plain,
    ( spl9_118
  <=> v1_funct_1(k5_relat_1(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_118])])).

fof(f1065,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ spl9_6
    | ~ spl9_110 ),
    inference(resolution,[],[f1009,f147])).

fof(f1077,plain,
    ( spl9_116
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f1064,f1008,f167,f178,f1075])).

fof(f1075,plain,
    ( spl9_116
  <=> v1_funct_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).

fof(f1064,plain,
    ( ~ v1_funct_1(sK3)
    | v1_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(resolution,[],[f1009,f168])).

fof(f1042,plain,
    ( spl9_114
    | ~ spl9_11
    | ~ spl9_6
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f1023,f1004,f146,f157,f1040])).

fof(f1040,plain,
    ( spl9_114
  <=> v1_funct_1(k5_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).

fof(f1023,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_1(k5_relat_1(sK4,sK3))
    | ~ spl9_6
    | ~ spl9_108 ),
    inference(resolution,[],[f1005,f147])).

fof(f1035,plain,
    ( spl9_112
    | ~ spl9_17
    | ~ spl9_12
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f1022,f1004,f167,f178,f1033])).

fof(f1033,plain,
    ( spl9_112
  <=> v1_funct_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_112])])).

fof(f1022,plain,
    ( ~ v1_funct_1(sK3)
    | v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ spl9_12
    | ~ spl9_108 ),
    inference(resolution,[],[f1005,f168])).

fof(f1010,plain,
    ( ~ spl9_11
    | spl9_110
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f997,f146,f1008,f157])).

fof(f997,plain,
    ( ! [X101,X99,X100] :
        ( v1_funct_1(k5_relat_1(X99,sK4))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X99,k1_zfmisc_1(k2_zfmisc_1(X100,X101)))
        | ~ v1_funct_1(X99) )
    | ~ spl9_6 ),
    inference(resolution,[],[f682,f147])).

fof(f1006,plain,
    ( ~ spl9_17
    | spl9_108
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f996,f167,f1004,f178])).

fof(f996,plain,
    ( ! [X97,X98,X96] :
        ( v1_funct_1(k5_relat_1(X96,sK3))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X97,X98)))
        | ~ v1_funct_1(X96) )
    | ~ spl9_12 ),
    inference(resolution,[],[f682,f168])).

fof(f709,plain,
    ( spl9_82
    | spl9_106
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f705,f146,f707,f493])).

fof(f707,plain,
    ( spl9_106
  <=> ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK4,X0))
        | r2_hidden(sK6(sK6(k1_zfmisc_1(k10_relat_1(sK4,X0)))),u1_struct_0(sK2))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK4,X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f705,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK4,X0))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK4,X0))))
        | v1_xboole_0(u1_struct_0(sK2))
        | r2_hidden(sK6(sK6(k1_zfmisc_1(k10_relat_1(sK4,X0)))),u1_struct_0(sK2)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f505,f103])).

fof(f505,plain,
    ( ! [X1] :
        ( m1_subset_1(sK6(sK6(k1_zfmisc_1(k10_relat_1(sK4,X1)))),u1_struct_0(sK2))
        | v1_xboole_0(k10_relat_1(sK4,X1))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK4,X1)))) )
    | ~ spl9_6 ),
    inference(resolution,[],[f490,f445])).

fof(f701,plain,
    ( spl9_80
    | ~ spl9_79
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f550,f167,f484,f487])).

fof(f487,plain,
    ( spl9_80
  <=> ! [X3,X2] : ~ r2_hidden(X2,k10_relat_1(sK3,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f550,plain,
    ( ! [X2,X3] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f545,f111])).

fof(f545,plain,
    ( ! [X10] : m1_subset_1(k10_relat_1(sK3,X10),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_12 ),
    inference(resolution,[],[f470,f168])).

fof(f700,plain,
    ( spl9_80
    | ~ spl9_79
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f598,f273,f484,f487])).

fof(f598,plain,
    ( ! [X14,X13] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ r2_hidden(X13,k10_relat_1(sK3,X14)) )
    | ~ spl9_40 ),
    inference(resolution,[],[f585,f274])).

fof(f699,plain,
    ( spl9_80
    | ~ spl9_79
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f646,f167,f484,f487])).

fof(f646,plain,
    ( ! [X33,X34] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | ~ r2_hidden(X33,k10_relat_1(sK3,X34)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f640,f168])).

fof(f640,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | ~ r2_hidden(X4,k10_relat_1(X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f639])).

fof(f639,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k10_relat_1(X2,X3))
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f459,f113])).

fof(f698,plain,
    ( spl9_104
    | ~ spl9_79
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f655,f167,f484,f696])).

fof(f696,plain,
    ( spl9_104
  <=> ! [X28] : v1_xboole_0(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X28)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).

fof(f655,plain,
    ( ! [X28] :
        ( ~ v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,X28)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f637,f168])).

fof(f694,plain,
    ( spl9_78
    | spl9_102
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f690,f167,f692,f481])).

fof(f692,plain,
    ( spl9_102
  <=> ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK3,X0))
        | r2_hidden(sK6(sK6(k1_zfmisc_1(k10_relat_1(sK3,X0)))),u1_struct_0(sK0))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK3,X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).

fof(f690,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK3,X0))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK3,X0))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK6(sK6(k1_zfmisc_1(k10_relat_1(sK3,X0)))),u1_struct_0(sK0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f503,f103])).

fof(f503,plain,
    ( ! [X1] :
        ( m1_subset_1(sK6(sK6(k1_zfmisc_1(k10_relat_1(sK3,X1)))),u1_struct_0(sK0))
        | v1_xboole_0(k10_relat_1(sK3,X1))
        | v1_xboole_0(sK6(k1_zfmisc_1(k10_relat_1(sK3,X1)))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f478,f445])).

fof(f689,plain,
    ( ~ spl9_17
    | ~ spl9_13
    | ~ spl9_11
    | ~ spl9_7
    | ~ spl9_101
    | spl9_1 ),
    inference(avatar_split_clause,[],[f680,f125,f687,f143,f157,f164,f178])).

fof(f164,plain,
    ( spl9_13
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f143,plain,
    ( spl9_7
  <=> ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f687,plain,
    ( spl9_101
  <=> ~ v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_101])])).

fof(f125,plain,
    ( spl9_1
  <=> ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK4),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f680,plain,
    ( ~ v5_pre_topc(k5_relat_1(sK3,sK4),sK0,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ spl9_1 ),
    inference(superposition,[],[f126,f116])).

fof(f126,plain,
    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK4),sK0,sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f576,plain,
    ( spl9_96
    | spl9_98
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f566,f146,f574,f568])).

fof(f568,plain,
    ( spl9_96
  <=> ! [X5] : r2_hidden(k10_relat_1(sK4,X5),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f574,plain,
    ( spl9_98
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).

fof(f566,plain,
    ( ! [X5] :
        ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)))
        | r2_hidden(k10_relat_1(sK4,X5),k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl9_6 ),
    inference(resolution,[],[f546,f103])).

fof(f562,plain,
    ( spl9_92
    | spl9_94
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f552,f167,f560,f554])).

fof(f554,plain,
    ( spl9_92
  <=> ! [X5] : r2_hidden(k10_relat_1(sK3,X5),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f560,plain,
    ( spl9_94
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f552,plain,
    ( ! [X5] :
        ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k10_relat_1(sK3,X5),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f545,f103])).

fof(f528,plain,
    ( spl9_20
    | ~ spl9_35
    | ~ spl9_82 ),
    inference(avatar_split_clause,[],[f527,f493,f245,f192])).

fof(f192,plain,
    ( spl9_20
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f245,plain,
    ( spl9_35
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f527,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_82 ),
    inference(resolution,[],[f494,f98])).

fof(f494,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_82 ),
    inference(avatar_component_clause,[],[f493])).

fof(f526,plain,
    ( spl9_82
    | spl9_90
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f522,f146,f524,f493])).

fof(f524,plain,
    ( spl9_90
  <=> ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK4,X0))
        | r2_hidden(sK6(k10_relat_1(sK4,X0)),u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f522,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK4,X0))
        | v1_xboole_0(u1_struct_0(sK2))
        | r2_hidden(sK6(k10_relat_1(sK4,X0)),u1_struct_0(sK2)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f504,f103])).

fof(f504,plain,
    ( ! [X0] :
        ( m1_subset_1(sK6(k10_relat_1(sK4,X0)),u1_struct_0(sK2))
        | v1_xboole_0(k10_relat_1(sK4,X0)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f490,f280])).

fof(f521,plain,
    ( spl9_88
    | ~ spl9_31
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f514,f481,f231,f519])).

fof(f519,plain,
    ( spl9_88
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f231,plain,
    ( spl9_31
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f514,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_78 ),
    inference(resolution,[],[f482,f98])).

fof(f482,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_78 ),
    inference(avatar_component_clause,[],[f481])).

fof(f513,plain,
    ( spl9_78
    | spl9_86
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f509,f167,f511,f481])).

fof(f511,plain,
    ( spl9_86
  <=> ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK3,X0))
        | r2_hidden(sK6(k10_relat_1(sK3,X0)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f509,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK3,X0))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK6(k10_relat_1(sK3,X0)),u1_struct_0(sK0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f502,f103])).

fof(f502,plain,
    ( ! [X0] :
        ( m1_subset_1(sK6(k10_relat_1(sK3,X0)),u1_struct_0(sK0))
        | v1_xboole_0(k10_relat_1(sK3,X0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f478,f280])).

fof(f501,plain,
    ( ~ spl9_83
    | spl9_84
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f491,f146,f499,f496])).

fof(f496,plain,
    ( spl9_83
  <=> ~ v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).

fof(f499,plain,
    ( spl9_84
  <=> ! [X3,X2] : ~ r2_hidden(X2,k10_relat_1(sK4,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f491,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_relat_1(sK4,X3))
        | ~ v1_xboole_0(u1_struct_0(sK2)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f475,f342])).

fof(f489,plain,
    ( ~ spl9_79
    | spl9_80
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f479,f167,f487,f484])).

fof(f479,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_relat_1(sK3,X3))
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f474,f342])).

fof(f432,plain,
    ( ~ spl9_77
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f425,f391,f430])).

fof(f430,plain,
    ( spl9_77
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).

fof(f425,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),sK4)
    | ~ spl9_68 ),
    inference(duplicate_literal_removal,[],[f424])).

fof(f424,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),sK4)
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),sK4)
    | ~ spl9_68 ),
    inference(resolution,[],[f398,f392])).

fof(f422,plain,
    ( ~ spl9_73
    | ~ spl9_75
    | ~ spl9_64
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f401,f391,f377,f420,f414])).

fof(f420,plain,
    ( spl9_75
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_75])])).

fof(f401,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)),sK3)
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),sK4)
    | ~ spl9_64
    | ~ spl9_68 ),
    inference(resolution,[],[f395,f392])).

fof(f395,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),X1)
        | ~ r2_hidden(X1,sK3) )
    | ~ spl9_64 ),
    inference(resolution,[],[f378,f101])).

fof(f409,plain,
    ( ~ spl9_71
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f402,f377,f407])).

fof(f407,plain,
    ( spl9_71
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f402,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),sK3)
    | ~ spl9_64 ),
    inference(duplicate_literal_removal,[],[f400])).

fof(f400,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),sK3)
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)),sK3)
    | ~ spl9_64 ),
    inference(resolution,[],[f395,f378])).

fof(f393,plain,
    ( spl9_62
    | spl9_68
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f389,f146,f391,f360])).

fof(f389,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) )
    | ~ spl9_6 ),
    inference(resolution,[],[f372,f103])).

fof(f372,plain,
    ( ! [X4] :
        ( m1_subset_1(X4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | ~ r2_hidden(X4,sK4) )
    | ~ spl9_6 ),
    inference(resolution,[],[f110,f147])).

fof(f388,plain,
    ( spl9_66
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f381,f347,f386])).

fof(f386,plain,
    ( spl9_66
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f347,plain,
    ( spl9_56
  <=> ! [X3] : ~ r2_hidden(X3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f381,plain,
    ( v1_xboole_0(sK3)
    | ~ spl9_56 ),
    inference(resolution,[],[f348,f280])).

fof(f348,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK3)
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f347])).

fof(f380,plain,
    ( ~ spl9_59
    | spl9_56
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f369,f273,f347,f353])).

fof(f369,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK3)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) )
    | ~ spl9_40 ),
    inference(resolution,[],[f342,f274])).

fof(f379,plain,
    ( spl9_58
    | spl9_64
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f375,f167,f377,f350])).

fof(f375,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f371,f103])).

fof(f371,plain,
    ( ! [X3] :
        ( m1_subset_1(X3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ r2_hidden(X3,sK3) )
    | ~ spl9_12 ),
    inference(resolution,[],[f110,f168])).

fof(f365,plain,
    ( spl9_60
    | ~ spl9_63
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f344,f146,f363,f357])).

fof(f344,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
        | ~ r2_hidden(X4,sK4) )
    | ~ spl9_6 ),
    inference(resolution,[],[f111,f147])).

fof(f355,plain,
    ( spl9_56
    | ~ spl9_59
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f343,f167,f353,f347])).

fof(f343,plain,
    ( ! [X3] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ r2_hidden(X3,sK3) )
    | ~ spl9_12 ),
    inference(resolution,[],[f111,f168])).

fof(f338,plain,
    ( spl9_54
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f323,f146,f336])).

fof(f336,plain,
    ( spl9_54
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f323,plain,
    ( v1_relat_1(sK4)
    | ~ spl9_6 ),
    inference(resolution,[],[f109,f147])).

fof(f331,plain,
    ( spl9_52
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f322,f167,f329])).

fof(f329,plain,
    ( spl9_52
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f322,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_12 ),
    inference(resolution,[],[f109,f168])).

fof(f320,plain,
    ( ~ spl9_49
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f312,f298,f301])).

fof(f301,plain,
    ( spl9_49
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f298,plain,
    ( spl9_46
  <=> r2_hidden(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f312,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl9_46 ),
    inference(resolution,[],[f299,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t7_boole)).

fof(f299,plain,
    ( r2_hidden(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f298])).

fof(f319,plain,
    ( ~ spl9_51
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f311,f298,f317])).

fof(f317,plain,
    ( spl9_51
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f311,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))),sK4)
    | ~ spl9_46 ),
    inference(resolution,[],[f299,f101])).

fof(f306,plain,
    ( spl9_46
    | spl9_48
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f279,f146,f304,f298])).

fof(f304,plain,
    ( spl9_48
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f279,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_hidden(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl9_6 ),
    inference(resolution,[],[f103,f147])).

fof(f293,plain,
    ( spl9_42
    | spl9_44
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f278,f167,f291,f285])).

fof(f285,plain,
    ( spl9_42
  <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f291,plain,
    ( spl9_44
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f278,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ spl9_12 ),
    inference(resolution,[],[f103,f168])).

fof(f275,plain,
    ( spl9_40
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f261,f167,f273])).

fof(f261,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
    | ~ spl9_12 ),
    inference(resolution,[],[f105,f168])).

fof(f268,plain,
    ( spl9_38
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f260,f146,f266])).

fof(f260,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ spl9_6 ),
    inference(resolution,[],[f105,f147])).

fof(f257,plain,
    ( spl9_36
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f229,f223,f255])).

fof(f255,plain,
    ( spl9_36
  <=> l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f223,plain,
    ( spl9_28
  <=> l1_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f229,plain,
    ( l1_struct_0(sK8)
    | ~ spl9_28 ),
    inference(resolution,[],[f93,f224])).

fof(f224,plain,
    ( l1_pre_topc(sK8)
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f223])).

fof(f93,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',dt_l1_pre_topc)).

fof(f250,plain,
    ( spl9_34
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f228,f188,f248])).

fof(f248,plain,
    ( spl9_34
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f188,plain,
    ( spl9_18
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f228,plain,
    ( l1_struct_0(sK2)
    | ~ spl9_18 ),
    inference(resolution,[],[f93,f189])).

fof(f189,plain,
    ( l1_pre_topc(sK2)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f243,plain,
    ( spl9_32
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f227,f202,f241])).

fof(f241,plain,
    ( spl9_32
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f202,plain,
    ( spl9_22
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f227,plain,
    ( l1_struct_0(sK1)
    | ~ spl9_22 ),
    inference(resolution,[],[f93,f203])).

fof(f203,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f202])).

fof(f236,plain,
    ( spl9_30
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f226,f209,f234])).

fof(f234,plain,
    ( spl9_30
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f209,plain,
    ( spl9_24
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f226,plain,
    ( l1_struct_0(sK0)
    | ~ spl9_24 ),
    inference(resolution,[],[f93,f210])).

fof(f210,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f209])).

fof(f225,plain,(
    spl9_28 ),
    inference(avatar_split_clause,[],[f120,f223])).

fof(f120,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    l1_pre_topc(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f77])).

fof(f77,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK8) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',existence_l1_pre_topc)).

fof(f218,plain,(
    spl9_26 ),
    inference(avatar_split_clause,[],[f119,f216])).

fof(f216,plain,
    ( spl9_26
  <=> l1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f119,plain,(
    l1_struct_0(sK7) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    l1_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f17,f75])).

fof(f75,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK7) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',existence_l1_struct_0)).

fof(f211,plain,(
    spl9_24 ),
    inference(avatar_split_clause,[],[f79,f209])).

fof(f79,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK4),sK0,sK1)
    & v5_pre_topc(sK4,sK2,sK1)
    & v5_pre_topc(sK3,sK0,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f66,f65,f64,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                        & v5_pre_topc(X4,X2,X1)
                        & v5_pre_topc(X3,X0,X2)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                & l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),sK0,X1)
                      & v5_pre_topc(X4,X2,X1)
                      & v5_pre_topc(X3,sK0,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                      & v5_pre_topc(X4,X2,X1)
                      & v5_pre_topc(X3,X0,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(sK1),X3,X4),X0,sK1)
                    & v5_pre_topc(X4,X2,sK1)
                    & v5_pre_topc(X3,X0,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                & v1_funct_1(X3) )
            & l1_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                  & v5_pre_topc(X4,X2,X1)
                  & v5_pre_topc(X3,X0,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
              & v1_funct_1(X3) )
          & l1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(X1),X3,X4),X0,X1)
                & v5_pre_topc(X4,sK2,X1)
                & v5_pre_topc(X3,X0,sK2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X3) )
        & l1_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
              & v5_pre_topc(X4,X2,X1)
              & v5_pre_topc(X3,X0,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),sK3,X4),X0,X1)
            & v5_pre_topc(X4,X2,X1)
            & v5_pre_topc(sK3,X0,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X2))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
          & v5_pre_topc(X4,X2,X1)
          & v5_pre_topc(X3,X0,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,sK4),X0,X1)
        & v5_pre_topc(sK4,X2,X1)
        & v5_pre_topc(X3,X0,X2)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                      & v5_pre_topc(X4,X2,X1)
                      & v5_pre_topc(X3,X0,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1)
                      & v5_pre_topc(X4,X2,X1)
                      & v5_pre_topc(X3,X0,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( v5_pre_topc(X4,X2,X1)
                            & v5_pre_topc(X3,X0,X2) )
                         => v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( v5_pre_topc(X4,X2,X1)
                          & v5_pre_topc(X3,X0,X2) )
                       => v5_pre_topc(k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X0,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t58_tops_2.p',t58_tops_2)).

fof(f204,plain,(
    spl9_22 ),
    inference(avatar_split_clause,[],[f80,f202])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f197,plain,(
    ~ spl9_21 ),
    inference(avatar_split_clause,[],[f81,f195])).

fof(f195,plain,
    ( spl9_21
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f81,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f190,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f82,f188])).

fof(f82,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f183,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f83,f181])).

fof(f181,plain,
    ( spl9_16
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f83,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f176,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f84,f174])).

fof(f174,plain,
    ( spl9_14
  <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f84,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f67])).

fof(f169,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f85,f167])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f67])).

fof(f162,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f86,f160])).

fof(f160,plain,
    ( spl9_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f86,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f155,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f87,f153])).

fof(f153,plain,
    ( spl9_8
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f87,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f67])).

fof(f148,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f88,f146])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f67])).

fof(f141,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f89,f139])).

fof(f139,plain,
    ( spl9_4
  <=> v5_pre_topc(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f89,plain,(
    v5_pre_topc(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f134,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f90,f132])).

fof(f132,plain,
    ( spl9_2
  <=> v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f90,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f127,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f91,f125])).

fof(f91,plain,(
    ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK4),sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
