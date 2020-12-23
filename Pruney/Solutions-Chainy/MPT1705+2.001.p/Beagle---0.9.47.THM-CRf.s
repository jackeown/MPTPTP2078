%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:24 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :  179 (2128 expanded)
%              Number of leaves         :   25 ( 743 expanded)
%              Depth                    :   17
%              Number of atoms          :  430 (8761 expanded)
%              Number of equality atoms :  105 (1896 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( C = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                 => ( ( v1_tsep_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_tsep_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_59,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_30,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_26,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_85,plain,(
    ! [A_33] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_33),u1_pre_topc(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_85])).

tff(c_93,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_91])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_2] :
      ( m1_subset_1(u1_pre_topc(A_2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2))))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_772,plain,(
    ! [C_103,A_104,D_105,B_106] :
      ( C_103 = A_104
      | g1_pre_topc(C_103,D_105) != g1_pre_topc(A_104,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(A_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_781,plain,(
    ! [A_107,B_108] :
      ( u1_struct_0('#skF_2') = A_107
      | g1_pre_topc(A_107,B_108) != '#skF_3'
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k1_zfmisc_1(A_107))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_772])).

tff(c_786,plain,(
    ! [A_109] :
      ( u1_struct_0(A_109) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_109),u1_pre_topc(A_109)) != '#skF_3'
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_4,c_781])).

tff(c_827,plain,(
    ! [A_117] :
      ( u1_struct_0(A_117) = u1_struct_0('#skF_2')
      | A_117 != '#skF_3'
      | ~ l1_pre_topc(A_117)
      | ~ v1_pre_topc(A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_786])).

tff(c_830,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_827])).

tff(c_836,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_830])).

tff(c_780,plain,(
    ! [C_103,D_105] :
      ( u1_struct_0('#skF_2') = C_103
      | g1_pre_topc(C_103,D_105) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_772])).

tff(c_838,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_780])).

tff(c_895,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_838])).

tff(c_864,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_4])).

tff(c_879,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_864])).

tff(c_910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_895,c_879])).

tff(c_912,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_780])).

tff(c_981,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_912])).

tff(c_801,plain,(
    ! [D_110,B_111,C_112,A_113] :
      ( D_110 = B_111
      | g1_pre_topc(C_112,D_110) != g1_pre_topc(A_113,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k1_zfmisc_1(A_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_809,plain,(
    ! [D_110,C_112] :
      ( u1_pre_topc('#skF_2') = D_110
      | g1_pre_topc(C_112,D_110) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_801])).

tff(c_967,plain,(
    ! [D_110,C_112] :
      ( u1_pre_topc('#skF_2') = D_110
      | g1_pre_topc(C_112,D_110) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_809])).

tff(c_968,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_968])).

tff(c_1027,plain,(
    ! [D_126,C_127] :
      ( u1_pre_topc('#skF_2') = D_126
      | g1_pre_topc(C_127,D_126) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_1083,plain,(
    ! [A_132] :
      ( u1_pre_topc(A_132) = u1_pre_topc('#skF_2')
      | A_132 != '#skF_3'
      | ~ v1_pre_topc(A_132)
      | ~ l1_pre_topc(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1027])).

tff(c_1086,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_1083])).

tff(c_1092,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1086])).

tff(c_916,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_26])).

tff(c_1097,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_916])).

tff(c_1221,plain,(
    ! [C_140,A_141] :
      ( m1_pre_topc(C_140,A_141)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_140),u1_pre_topc(C_140)),A_141)
      | ~ l1_pre_topc(C_140)
      | ~ v2_pre_topc(C_140)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_140),u1_pre_topc(C_140)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_140),u1_pre_topc(C_140)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1233,plain,(
    ! [A_141] :
      ( m1_pre_topc('#skF_2',A_141)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_141)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_1221])).

tff(c_1244,plain,(
    ! [A_142] :
      ( m1_pre_topc('#skF_2',A_142)
      | ~ m1_pre_topc('#skF_3',A_142)
      | ~ l1_pre_topc(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1097,c_1092,c_836,c_28,c_1097,c_1092,c_836,c_34,c_32,c_1097,c_1092,c_1233])).

tff(c_112,plain,(
    ! [C_37,A_38,D_39,B_40] :
      ( C_37 = A_38
      | g1_pre_topc(C_37,D_39) != g1_pre_topc(A_38,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_120,plain,(
    ! [C_37,D_39] :
      ( u1_struct_0('#skF_2') = C_37
      | g1_pre_topc(C_37,D_39) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_112])).

tff(c_155,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_158,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_155])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_158])).

tff(c_165,plain,(
    ! [C_50,D_51] :
      ( u1_struct_0('#skF_2') = C_50
      | g1_pre_topc(C_50,D_51) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_182,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = u1_struct_0('#skF_2')
      | A_52 != '#skF_3'
      | ~ v1_pre_topc(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_165])).

tff(c_185,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_182])).

tff(c_191,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_185])).

tff(c_164,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_194,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_164])).

tff(c_125,plain,(
    ! [D_41,B_42,C_43,A_44] :
      ( D_41 = B_42
      | g1_pre_topc(C_43,D_41) != g1_pre_topc(A_44,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_133,plain,(
    ! [D_41,C_43] :
      ( u1_pre_topc('#skF_2') = D_41
      | g1_pre_topc(C_43,D_41) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_125])).

tff(c_257,plain,(
    ! [D_41,C_43] :
      ( u1_pre_topc('#skF_2') = D_41
      | g1_pre_topc(C_43,D_41) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_133])).

tff(c_258,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_258])).

tff(c_309,plain,(
    ! [D_61,C_62] :
      ( u1_pre_topc('#skF_2') = D_61
      | g1_pre_topc(C_62,D_61) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_351,plain,(
    ! [A_65] :
      ( u1_pre_topc(A_65) = u1_pre_topc('#skF_2')
      | A_65 != '#skF_3'
      | ~ v1_pre_topc(A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_309])).

tff(c_354,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_351])).

tff(c_360,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_354])).

tff(c_196,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_26])).

tff(c_374,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_196])).

tff(c_461,plain,(
    ! [C_71,A_72] :
      ( m1_pre_topc(C_71,A_72)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_71),u1_pre_topc(C_71)),A_72)
      | ~ l1_pre_topc(C_71)
      | ~ v2_pre_topc(C_71)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_71),u1_pre_topc(C_71)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_71),u1_pre_topc(C_71)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_473,plain,(
    ! [A_72] :
      ( m1_pre_topc('#skF_2',A_72)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_72)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_461])).

tff(c_483,plain,(
    ! [A_72] :
      ( m1_pre_topc('#skF_2',A_72)
      | ~ m1_pre_topc('#skF_3',A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_374,c_360,c_191,c_28,c_374,c_360,c_191,c_34,c_32,c_374,c_360,c_473])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_56,plain,
    ( v1_tsep_1('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_57,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_24,plain,(
    ! [B_26,A_24] :
      ( m1_subset_1(u1_struct_0(B_26),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_295,plain,(
    ! [B_59,A_60] :
      ( v3_pre_topc(u1_struct_0(B_59),A_60)
      | ~ v1_tsep_1(B_59,A_60)
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_pre_topc(B_59,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_308,plain,(
    ! [B_26,A_24] :
      ( v3_pre_topc(u1_struct_0(B_26),A_24)
      | ~ v1_tsep_1(B_26,A_24)
      | ~ v2_pre_topc(A_24)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_295])).

tff(c_229,plain,(
    ! [B_53,A_54] :
      ( v1_tsep_1(B_53,A_54)
      | ~ v3_pre_topc(u1_struct_0(B_53),A_54)
      | ~ m1_subset_1(u1_struct_0(B_53),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_550,plain,(
    ! [B_80,A_81] :
      ( v1_tsep_1(B_80,A_81)
      | ~ v3_pre_topc(u1_struct_0(B_80),A_81)
      | ~ v2_pre_topc(A_81)
      | ~ m1_pre_topc(B_80,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_24,c_229])).

tff(c_576,plain,(
    ! [A_83] :
      ( v1_tsep_1('#skF_2',A_83)
      | ~ v3_pre_topc(u1_struct_0('#skF_3'),A_83)
      | ~ v2_pre_topc(A_83)
      | ~ m1_pre_topc('#skF_2',A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_550])).

tff(c_727,plain,(
    ! [A_96] :
      ( v1_tsep_1('#skF_2',A_96)
      | ~ m1_pre_topc('#skF_2',A_96)
      | ~ v1_tsep_1('#skF_3',A_96)
      | ~ v2_pre_topc(A_96)
      | ~ m1_pre_topc('#skF_3',A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_308,c_576])).

tff(c_40,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_96,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_59,c_40])).

tff(c_97,plain,(
    ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_733,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_727,c_97])).

tff(c_737,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_59,c_38,c_57,c_733])).

tff(c_751,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_483,c_737])).

tff(c_755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_59,c_751])).

tff(c_756,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1253,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1244,c_756])).

tff(c_1261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_59,c_1253])).

tff(c_1263,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1262,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1270,plain,(
    ! [A_144] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_144),u1_pre_topc(A_144)))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1273,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1270])).

tff(c_1275,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1273])).

tff(c_1356,plain,(
    ! [D_157,B_158,C_159,A_160] :
      ( D_157 = B_158
      | g1_pre_topc(C_159,D_157) != g1_pre_topc(A_160,B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(k1_zfmisc_1(A_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1414,plain,(
    ! [B_161,A_162] :
      ( u1_pre_topc('#skF_2') = B_161
      | g1_pre_topc(A_162,B_161) != '#skF_3'
      | ~ m1_subset_1(B_161,k1_zfmisc_1(k1_zfmisc_1(A_162))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1356])).

tff(c_1462,plain,(
    ! [A_167] :
      ( u1_pre_topc(A_167) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_167),u1_pre_topc(A_167)) != '#skF_3'
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_4,c_1414])).

tff(c_1473,plain,(
    ! [A_168] :
      ( u1_pre_topc(A_168) = u1_pre_topc('#skF_2')
      | A_168 != '#skF_3'
      | ~ l1_pre_topc(A_168)
      | ~ v1_pre_topc(A_168)
      | ~ l1_pre_topc(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1462])).

tff(c_1476,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1275,c_1473])).

tff(c_1482,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1476])).

tff(c_1315,plain,(
    ! [C_149,A_150,D_151,B_152] :
      ( C_149 = A_150
      | g1_pre_topc(C_149,D_151) != g1_pre_topc(A_150,B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(k1_zfmisc_1(A_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1324,plain,(
    ! [A_153,B_154] :
      ( u1_struct_0('#skF_2') = A_153
      | g1_pre_topc(A_153,B_154) != '#skF_3'
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k1_zfmisc_1(A_153))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1315])).

tff(c_1329,plain,(
    ! [A_155] :
      ( u1_struct_0(A_155) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_155),u1_pre_topc(A_155)) != '#skF_3'
      | ~ l1_pre_topc(A_155) ) ),
    inference(resolution,[status(thm)],[c_4,c_1324])).

tff(c_1341,plain,(
    ! [A_156] :
      ( u1_struct_0(A_156) = u1_struct_0('#skF_2')
      | A_156 != '#skF_3'
      | ~ l1_pre_topc(A_156)
      | ~ v1_pre_topc(A_156)
      | ~ l1_pre_topc(A_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1329])).

tff(c_1344,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1275,c_1341])).

tff(c_1350,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1344])).

tff(c_1368,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1350,c_26])).

tff(c_1498,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1482,c_1368])).

tff(c_1662,plain,(
    ! [C_183,A_184] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(C_183),u1_pre_topc(C_183)),A_184)
      | ~ m1_pre_topc(C_183,A_184)
      | ~ l1_pre_topc(C_183)
      | ~ v2_pre_topc(C_183)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_183),u1_pre_topc(C_183)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_183),u1_pre_topc(C_183)))
      | ~ l1_pre_topc(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1671,plain,(
    ! [A_184] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')),A_184)
      | ~ m1_pre_topc('#skF_2',A_184)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1482,c_1662])).

tff(c_1685,plain,(
    ! [A_185] :
      ( m1_pre_topc('#skF_3',A_185)
      | ~ m1_pre_topc('#skF_2',A_185)
      | ~ l1_pre_topc(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1498,c_1482,c_1350,c_28,c_1498,c_1482,c_1350,c_34,c_32,c_1498,c_1350,c_1671])).

tff(c_1691,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1262,c_1685])).

tff(c_1695,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1691])).

tff(c_1697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1263,c_1695])).

tff(c_1699,plain,(
    ~ v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1700,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1699,c_54])).

tff(c_1727,plain,(
    ! [A_188] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_188),u1_pre_topc(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1733,plain,
    ( v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1727])).

tff(c_1735,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1733])).

tff(c_1753,plain,(
    ! [C_192,A_193,D_194,B_195] :
      ( C_192 = A_193
      | g1_pre_topc(C_192,D_194) != g1_pre_topc(A_193,B_195)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(k1_zfmisc_1(A_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1761,plain,(
    ! [C_192,D_194] :
      ( u1_struct_0('#skF_2') = C_192
      | g1_pre_topc(C_192,D_194) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1753])).

tff(c_1807,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1761])).

tff(c_1810,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_1807])).

tff(c_1814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1810])).

tff(c_1817,plain,(
    ! [C_206,D_207] :
      ( u1_struct_0('#skF_2') = C_206
      | g1_pre_topc(C_206,D_207) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_1761])).

tff(c_1834,plain,(
    ! [A_208] :
      ( u1_struct_0(A_208) = u1_struct_0('#skF_2')
      | A_208 != '#skF_3'
      | ~ v1_pre_topc(A_208)
      | ~ l1_pre_topc(A_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1817])).

tff(c_1837,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1735,c_1834])).

tff(c_1843,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1837])).

tff(c_1816,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1761])).

tff(c_1846,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_1816])).

tff(c_1771,plain,(
    ! [D_198,B_199,C_200,A_201] :
      ( D_198 = B_199
      | g1_pre_topc(C_200,D_198) != g1_pre_topc(A_201,B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k1_zfmisc_1(A_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1779,plain,(
    ! [D_198,C_200] :
      ( u1_pre_topc('#skF_2') = D_198
      | g1_pre_topc(C_200,D_198) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1771])).

tff(c_1915,plain,(
    ! [D_198,C_200] :
      ( u1_pre_topc('#skF_2') = D_198
      | g1_pre_topc(C_200,D_198) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_1779])).

tff(c_1916,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_1915])).

tff(c_1934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1846,c_1916])).

tff(c_1967,plain,(
    ! [D_217,C_218] :
      ( u1_pre_topc('#skF_2') = D_217
      | g1_pre_topc(C_218,D_217) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_1915])).

tff(c_2009,plain,(
    ! [A_221] :
      ( u1_pre_topc(A_221) = u1_pre_topc('#skF_2')
      | A_221 != '#skF_3'
      | ~ v1_pre_topc(A_221)
      | ~ l1_pre_topc(A_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1967])).

tff(c_2012,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1735,c_2009])).

tff(c_2018,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2012])).

tff(c_1848,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1843,c_26])).

tff(c_2032,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2018,c_1848])).

tff(c_2126,plain,(
    ! [C_227,A_228] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(C_227),u1_pre_topc(C_227)),A_228)
      | ~ m1_pre_topc(C_227,A_228)
      | ~ l1_pre_topc(C_227)
      | ~ v2_pre_topc(C_227)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_227),u1_pre_topc(C_227)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_227),u1_pre_topc(C_227)))
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2138,plain,(
    ! [A_228] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_228)
      | ~ m1_pre_topc('#skF_2',A_228)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1843,c_2126])).

tff(c_2149,plain,(
    ! [A_229] :
      ( m1_pre_topc('#skF_3',A_229)
      | ~ m1_pre_topc('#skF_2',A_229)
      | ~ l1_pre_topc(A_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2032,c_2018,c_1843,c_28,c_2032,c_2018,c_1843,c_34,c_32,c_2032,c_2018,c_2138])).

tff(c_2155,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1700,c_2149])).

tff(c_2159,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2155])).

tff(c_1698,plain,(
    v1_tsep_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1887,plain,(
    ! [B_209,A_210] :
      ( v3_pre_topc(u1_struct_0(B_209),A_210)
      | ~ v1_tsep_1(B_209,A_210)
      | ~ m1_subset_1(u1_struct_0(B_209),k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ m1_pre_topc(B_209,A_210)
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2215,plain,(
    ! [B_236,A_237] :
      ( v3_pre_topc(u1_struct_0(B_236),A_237)
      | ~ v1_tsep_1(B_236,A_237)
      | ~ v2_pre_topc(A_237)
      | ~ m1_pre_topc(B_236,A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(resolution,[status(thm)],[c_24,c_1887])).

tff(c_2243,plain,(
    ! [A_239] :
      ( v3_pre_topc(u1_struct_0('#skF_3'),A_239)
      | ~ v1_tsep_1('#skF_2',A_239)
      | ~ v2_pre_topc(A_239)
      | ~ m1_pre_topc('#skF_2',A_239)
      | ~ l1_pre_topc(A_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1843,c_2215])).

tff(c_1953,plain,(
    ! [B_215,A_216] :
      ( v1_tsep_1(B_215,A_216)
      | ~ v3_pre_topc(u1_struct_0(B_215),A_216)
      | ~ m1_subset_1(u1_struct_0(B_215),k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ m1_pre_topc(B_215,A_216)
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1966,plain,(
    ! [B_26,A_24] :
      ( v1_tsep_1(B_26,A_24)
      | ~ v3_pre_topc(u1_struct_0(B_26),A_24)
      | ~ v2_pre_topc(A_24)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_1953])).

tff(c_2402,plain,(
    ! [A_255] :
      ( v1_tsep_1('#skF_3',A_255)
      | ~ m1_pre_topc('#skF_3',A_255)
      | ~ v1_tsep_1('#skF_2',A_255)
      | ~ v2_pre_topc(A_255)
      | ~ m1_pre_topc('#skF_2',A_255)
      | ~ l1_pre_topc(A_255) ) ),
    inference(resolution,[status(thm)],[c_2243,c_1966])).

tff(c_2408,plain,
    ( v1_tsep_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1698,c_2402])).

tff(c_2412,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1700,c_38,c_2159,c_2408])).

tff(c_2414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1699,c_2412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.82  
% 4.46/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.82  %$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.46/1.82  
% 4.46/1.82  %Foreground sorts:
% 4.46/1.82  
% 4.46/1.82  
% 4.46/1.82  %Background operators:
% 4.46/1.82  
% 4.46/1.82  
% 4.46/1.82  %Foreground operators:
% 4.46/1.82  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.46/1.82  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.46/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.82  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.46/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.46/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.46/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.46/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.46/1.82  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.46/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.46/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.82  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.46/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.82  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.46/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.46/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.46/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.46/1.82  
% 4.46/1.85  tff(f_120, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (v1_tsep_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tmap_1)).
% 4.46/1.85  tff(f_43, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 4.46/1.85  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 4.46/1.85  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.46/1.85  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 4.46/1.85  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 4.46/1.85  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.46/1.85  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.46/1.85  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_48, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_59, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 4.46/1.85  tff(c_30, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_28, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_26, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_85, plain, (![A_33]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_33), u1_pre_topc(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.46/1.85  tff(c_91, plain, (v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_85])).
% 4.46/1.85  tff(c_93, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_91])).
% 4.46/1.85  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.85  tff(c_4, plain, (![A_2]: (m1_subset_1(u1_pre_topc(A_2), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2)))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.46/1.85  tff(c_772, plain, (![C_103, A_104, D_105, B_106]: (C_103=A_104 | g1_pre_topc(C_103, D_105)!=g1_pre_topc(A_104, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(k1_zfmisc_1(A_104))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.46/1.85  tff(c_781, plain, (![A_107, B_108]: (u1_struct_0('#skF_2')=A_107 | g1_pre_topc(A_107, B_108)!='#skF_3' | ~m1_subset_1(B_108, k1_zfmisc_1(k1_zfmisc_1(A_107))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_772])).
% 4.46/1.85  tff(c_786, plain, (![A_109]: (u1_struct_0(A_109)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_109), u1_pre_topc(A_109))!='#skF_3' | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_4, c_781])).
% 4.46/1.85  tff(c_827, plain, (![A_117]: (u1_struct_0(A_117)=u1_struct_0('#skF_2') | A_117!='#skF_3' | ~l1_pre_topc(A_117) | ~v1_pre_topc(A_117) | ~l1_pre_topc(A_117))), inference(superposition, [status(thm), theory('equality')], [c_2, c_786])).
% 4.46/1.85  tff(c_830, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_93, c_827])).
% 4.46/1.85  tff(c_836, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_830])).
% 4.46/1.85  tff(c_780, plain, (![C_103, D_105]: (u1_struct_0('#skF_2')=C_103 | g1_pre_topc(C_103, D_105)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_772])).
% 4.46/1.85  tff(c_838, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_780])).
% 4.46/1.85  tff(c_895, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_836, c_838])).
% 4.46/1.85  tff(c_864, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_836, c_4])).
% 4.46/1.85  tff(c_879, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_864])).
% 4.46/1.85  tff(c_910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_895, c_879])).
% 4.46/1.85  tff(c_912, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_780])).
% 4.46/1.85  tff(c_981, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_836, c_912])).
% 4.46/1.85  tff(c_801, plain, (![D_110, B_111, C_112, A_113]: (D_110=B_111 | g1_pre_topc(C_112, D_110)!=g1_pre_topc(A_113, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(k1_zfmisc_1(A_113))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.46/1.85  tff(c_809, plain, (![D_110, C_112]: (u1_pre_topc('#skF_2')=D_110 | g1_pre_topc(C_112, D_110)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_801])).
% 4.46/1.85  tff(c_967, plain, (![D_110, C_112]: (u1_pre_topc('#skF_2')=D_110 | g1_pre_topc(C_112, D_110)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_836, c_809])).
% 4.46/1.85  tff(c_968, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_967])).
% 4.46/1.85  tff(c_990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_981, c_968])).
% 4.46/1.85  tff(c_1027, plain, (![D_126, C_127]: (u1_pre_topc('#skF_2')=D_126 | g1_pre_topc(C_127, D_126)!='#skF_3')), inference(splitRight, [status(thm)], [c_967])).
% 4.46/1.85  tff(c_1083, plain, (![A_132]: (u1_pre_topc(A_132)=u1_pre_topc('#skF_2') | A_132!='#skF_3' | ~v1_pre_topc(A_132) | ~l1_pre_topc(A_132))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1027])).
% 4.46/1.85  tff(c_1086, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_93, c_1083])).
% 4.46/1.85  tff(c_1092, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1086])).
% 4.46/1.85  tff(c_916, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_836, c_26])).
% 4.46/1.85  tff(c_1097, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_916])).
% 4.46/1.85  tff(c_1221, plain, (![C_140, A_141]: (m1_pre_topc(C_140, A_141) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_140), u1_pre_topc(C_140)), A_141) | ~l1_pre_topc(C_140) | ~v2_pre_topc(C_140) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_140), u1_pre_topc(C_140))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_140), u1_pre_topc(C_140))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.46/1.85  tff(c_1233, plain, (![A_141]: (m1_pre_topc('#skF_2', A_141) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_141) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_141))), inference(superposition, [status(thm), theory('equality')], [c_836, c_1221])).
% 4.46/1.85  tff(c_1244, plain, (![A_142]: (m1_pre_topc('#skF_2', A_142) | ~m1_pre_topc('#skF_3', A_142) | ~l1_pre_topc(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1097, c_1092, c_836, c_28, c_1097, c_1092, c_836, c_34, c_32, c_1097, c_1092, c_1233])).
% 4.46/1.85  tff(c_112, plain, (![C_37, A_38, D_39, B_40]: (C_37=A_38 | g1_pre_topc(C_37, D_39)!=g1_pre_topc(A_38, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_38))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.46/1.85  tff(c_120, plain, (![C_37, D_39]: (u1_struct_0('#skF_2')=C_37 | g1_pre_topc(C_37, D_39)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_112])).
% 4.46/1.85  tff(c_155, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_120])).
% 4.46/1.85  tff(c_158, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_155])).
% 4.46/1.85  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_158])).
% 4.46/1.85  tff(c_165, plain, (![C_50, D_51]: (u1_struct_0('#skF_2')=C_50 | g1_pre_topc(C_50, D_51)!='#skF_3')), inference(splitRight, [status(thm)], [c_120])).
% 4.46/1.85  tff(c_182, plain, (![A_52]: (u1_struct_0(A_52)=u1_struct_0('#skF_2') | A_52!='#skF_3' | ~v1_pre_topc(A_52) | ~l1_pre_topc(A_52))), inference(superposition, [status(thm), theory('equality')], [c_2, c_165])).
% 4.46/1.85  tff(c_185, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_93, c_182])).
% 4.46/1.85  tff(c_191, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_185])).
% 4.46/1.85  tff(c_164, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_120])).
% 4.46/1.85  tff(c_194, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_164])).
% 4.46/1.85  tff(c_125, plain, (![D_41, B_42, C_43, A_44]: (D_41=B_42 | g1_pre_topc(C_43, D_41)!=g1_pre_topc(A_44, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_44))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.46/1.85  tff(c_133, plain, (![D_41, C_43]: (u1_pre_topc('#skF_2')=D_41 | g1_pre_topc(C_43, D_41)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_125])).
% 4.46/1.85  tff(c_257, plain, (![D_41, C_43]: (u1_pre_topc('#skF_2')=D_41 | g1_pre_topc(C_43, D_41)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_133])).
% 4.46/1.85  tff(c_258, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_257])).
% 4.46/1.85  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_258])).
% 4.46/1.85  tff(c_309, plain, (![D_61, C_62]: (u1_pre_topc('#skF_2')=D_61 | g1_pre_topc(C_62, D_61)!='#skF_3')), inference(splitRight, [status(thm)], [c_257])).
% 4.46/1.85  tff(c_351, plain, (![A_65]: (u1_pre_topc(A_65)=u1_pre_topc('#skF_2') | A_65!='#skF_3' | ~v1_pre_topc(A_65) | ~l1_pre_topc(A_65))), inference(superposition, [status(thm), theory('equality')], [c_2, c_309])).
% 4.46/1.85  tff(c_354, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_93, c_351])).
% 4.46/1.85  tff(c_360, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_354])).
% 4.46/1.85  tff(c_196, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_26])).
% 4.46/1.85  tff(c_374, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_360, c_196])).
% 4.46/1.85  tff(c_461, plain, (![C_71, A_72]: (m1_pre_topc(C_71, A_72) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_71), u1_pre_topc(C_71)), A_72) | ~l1_pre_topc(C_71) | ~v2_pre_topc(C_71) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_71), u1_pre_topc(C_71))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_71), u1_pre_topc(C_71))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.46/1.85  tff(c_473, plain, (![A_72]: (m1_pre_topc('#skF_2', A_72) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_72) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_72))), inference(superposition, [status(thm), theory('equality')], [c_191, c_461])).
% 4.46/1.85  tff(c_483, plain, (![A_72]: (m1_pre_topc('#skF_2', A_72) | ~m1_pre_topc('#skF_3', A_72) | ~l1_pre_topc(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_374, c_360, c_191, c_28, c_374, c_360, c_191, c_34, c_32, c_374, c_360, c_473])).
% 4.46/1.85  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_56, plain, (v1_tsep_1('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_57, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 4.46/1.85  tff(c_24, plain, (![B_26, A_24]: (m1_subset_1(u1_struct_0(B_26), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.46/1.85  tff(c_295, plain, (![B_59, A_60]: (v3_pre_topc(u1_struct_0(B_59), A_60) | ~v1_tsep_1(B_59, A_60) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_pre_topc(B_59, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.46/1.85  tff(c_308, plain, (![B_26, A_24]: (v3_pre_topc(u1_struct_0(B_26), A_24) | ~v1_tsep_1(B_26, A_24) | ~v2_pre_topc(A_24) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_24, c_295])).
% 4.46/1.85  tff(c_229, plain, (![B_53, A_54]: (v1_tsep_1(B_53, A_54) | ~v3_pre_topc(u1_struct_0(B_53), A_54) | ~m1_subset_1(u1_struct_0(B_53), k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.46/1.85  tff(c_550, plain, (![B_80, A_81]: (v1_tsep_1(B_80, A_81) | ~v3_pre_topc(u1_struct_0(B_80), A_81) | ~v2_pre_topc(A_81) | ~m1_pre_topc(B_80, A_81) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_24, c_229])).
% 4.46/1.85  tff(c_576, plain, (![A_83]: (v1_tsep_1('#skF_2', A_83) | ~v3_pre_topc(u1_struct_0('#skF_3'), A_83) | ~v2_pre_topc(A_83) | ~m1_pre_topc('#skF_2', A_83) | ~l1_pre_topc(A_83))), inference(superposition, [status(thm), theory('equality')], [c_191, c_550])).
% 4.46/1.85  tff(c_727, plain, (![A_96]: (v1_tsep_1('#skF_2', A_96) | ~m1_pre_topc('#skF_2', A_96) | ~v1_tsep_1('#skF_3', A_96) | ~v2_pre_topc(A_96) | ~m1_pre_topc('#skF_3', A_96) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_308, c_576])).
% 4.46/1.85  tff(c_40, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_96, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_59, c_40])).
% 4.46/1.85  tff(c_97, plain, (~v1_tsep_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_96])).
% 4.46/1.85  tff(c_733, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_727, c_97])).
% 4.46/1.85  tff(c_737, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_59, c_38, c_57, c_733])).
% 4.46/1.85  tff(c_751, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_483, c_737])).
% 4.46/1.85  tff(c_755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_59, c_751])).
% 4.46/1.85  tff(c_756, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_96])).
% 4.46/1.85  tff(c_1253, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1244, c_756])).
% 4.46/1.85  tff(c_1261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_59, c_1253])).
% 4.46/1.85  tff(c_1263, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 4.46/1.85  tff(c_1262, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 4.46/1.85  tff(c_1270, plain, (![A_144]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_144), u1_pre_topc(A_144))) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.46/1.85  tff(c_1273, plain, (v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1270])).
% 4.46/1.85  tff(c_1275, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1273])).
% 4.46/1.85  tff(c_1356, plain, (![D_157, B_158, C_159, A_160]: (D_157=B_158 | g1_pre_topc(C_159, D_157)!=g1_pre_topc(A_160, B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(k1_zfmisc_1(A_160))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.46/1.85  tff(c_1414, plain, (![B_161, A_162]: (u1_pre_topc('#skF_2')=B_161 | g1_pre_topc(A_162, B_161)!='#skF_3' | ~m1_subset_1(B_161, k1_zfmisc_1(k1_zfmisc_1(A_162))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1356])).
% 4.46/1.85  tff(c_1462, plain, (![A_167]: (u1_pre_topc(A_167)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_167), u1_pre_topc(A_167))!='#skF_3' | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_4, c_1414])).
% 4.46/1.85  tff(c_1473, plain, (![A_168]: (u1_pre_topc(A_168)=u1_pre_topc('#skF_2') | A_168!='#skF_3' | ~l1_pre_topc(A_168) | ~v1_pre_topc(A_168) | ~l1_pre_topc(A_168))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1462])).
% 4.46/1.85  tff(c_1476, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1275, c_1473])).
% 4.46/1.85  tff(c_1482, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1476])).
% 4.46/1.85  tff(c_1315, plain, (![C_149, A_150, D_151, B_152]: (C_149=A_150 | g1_pre_topc(C_149, D_151)!=g1_pre_topc(A_150, B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(k1_zfmisc_1(A_150))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.46/1.85  tff(c_1324, plain, (![A_153, B_154]: (u1_struct_0('#skF_2')=A_153 | g1_pre_topc(A_153, B_154)!='#skF_3' | ~m1_subset_1(B_154, k1_zfmisc_1(k1_zfmisc_1(A_153))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1315])).
% 4.46/1.85  tff(c_1329, plain, (![A_155]: (u1_struct_0(A_155)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_155), u1_pre_topc(A_155))!='#skF_3' | ~l1_pre_topc(A_155))), inference(resolution, [status(thm)], [c_4, c_1324])).
% 4.46/1.85  tff(c_1341, plain, (![A_156]: (u1_struct_0(A_156)=u1_struct_0('#skF_2') | A_156!='#skF_3' | ~l1_pre_topc(A_156) | ~v1_pre_topc(A_156) | ~l1_pre_topc(A_156))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1329])).
% 4.46/1.85  tff(c_1344, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1275, c_1341])).
% 4.46/1.85  tff(c_1350, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1344])).
% 4.46/1.85  tff(c_1368, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1350, c_26])).
% 4.46/1.85  tff(c_1498, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1482, c_1368])).
% 4.46/1.85  tff(c_1662, plain, (![C_183, A_184]: (m1_pre_topc(g1_pre_topc(u1_struct_0(C_183), u1_pre_topc(C_183)), A_184) | ~m1_pre_topc(C_183, A_184) | ~l1_pre_topc(C_183) | ~v2_pre_topc(C_183) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_183), u1_pre_topc(C_183))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_183), u1_pre_topc(C_183))) | ~l1_pre_topc(A_184))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.46/1.85  tff(c_1671, plain, (![A_184]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3')), A_184) | ~m1_pre_topc('#skF_2', A_184) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_184))), inference(superposition, [status(thm), theory('equality')], [c_1482, c_1662])).
% 4.46/1.85  tff(c_1685, plain, (![A_185]: (m1_pre_topc('#skF_3', A_185) | ~m1_pre_topc('#skF_2', A_185) | ~l1_pre_topc(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1498, c_1482, c_1350, c_28, c_1498, c_1482, c_1350, c_34, c_32, c_1498, c_1350, c_1671])).
% 4.46/1.85  tff(c_1691, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1262, c_1685])).
% 4.46/1.85  tff(c_1695, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1691])).
% 4.46/1.85  tff(c_1697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1263, c_1695])).
% 4.46/1.85  tff(c_1699, plain, (~v1_tsep_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 4.46/1.85  tff(c_54, plain, (m1_pre_topc('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_1700, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1699, c_54])).
% 4.46/1.85  tff(c_1727, plain, (![A_188]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_188), u1_pre_topc(A_188))) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.46/1.85  tff(c_1733, plain, (v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1727])).
% 4.46/1.85  tff(c_1735, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1733])).
% 4.46/1.85  tff(c_1753, plain, (![C_192, A_193, D_194, B_195]: (C_192=A_193 | g1_pre_topc(C_192, D_194)!=g1_pre_topc(A_193, B_195) | ~m1_subset_1(B_195, k1_zfmisc_1(k1_zfmisc_1(A_193))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.46/1.85  tff(c_1761, plain, (![C_192, D_194]: (u1_struct_0('#skF_2')=C_192 | g1_pre_topc(C_192, D_194)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1753])).
% 4.46/1.85  tff(c_1807, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1761])).
% 4.46/1.85  tff(c_1810, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_1807])).
% 4.46/1.85  tff(c_1814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1810])).
% 4.46/1.85  tff(c_1817, plain, (![C_206, D_207]: (u1_struct_0('#skF_2')=C_206 | g1_pre_topc(C_206, D_207)!='#skF_3')), inference(splitRight, [status(thm)], [c_1761])).
% 4.46/1.85  tff(c_1834, plain, (![A_208]: (u1_struct_0(A_208)=u1_struct_0('#skF_2') | A_208!='#skF_3' | ~v1_pre_topc(A_208) | ~l1_pre_topc(A_208))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1817])).
% 4.46/1.85  tff(c_1837, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1735, c_1834])).
% 4.46/1.85  tff(c_1843, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1837])).
% 4.46/1.85  tff(c_1816, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_1761])).
% 4.46/1.85  tff(c_1846, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_1816])).
% 4.46/1.85  tff(c_1771, plain, (![D_198, B_199, C_200, A_201]: (D_198=B_199 | g1_pre_topc(C_200, D_198)!=g1_pre_topc(A_201, B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(k1_zfmisc_1(A_201))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.46/1.85  tff(c_1779, plain, (![D_198, C_200]: (u1_pre_topc('#skF_2')=D_198 | g1_pre_topc(C_200, D_198)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1771])).
% 4.46/1.85  tff(c_1915, plain, (![D_198, C_200]: (u1_pre_topc('#skF_2')=D_198 | g1_pre_topc(C_200, D_198)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_1779])).
% 4.46/1.85  tff(c_1916, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_1915])).
% 4.46/1.85  tff(c_1934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1846, c_1916])).
% 4.46/1.85  tff(c_1967, plain, (![D_217, C_218]: (u1_pre_topc('#skF_2')=D_217 | g1_pre_topc(C_218, D_217)!='#skF_3')), inference(splitRight, [status(thm)], [c_1915])).
% 4.46/1.85  tff(c_2009, plain, (![A_221]: (u1_pre_topc(A_221)=u1_pre_topc('#skF_2') | A_221!='#skF_3' | ~v1_pre_topc(A_221) | ~l1_pre_topc(A_221))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1967])).
% 4.46/1.85  tff(c_2012, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1735, c_2009])).
% 4.46/1.85  tff(c_2018, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2012])).
% 4.46/1.85  tff(c_1848, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1843, c_26])).
% 4.46/1.85  tff(c_2032, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2018, c_1848])).
% 4.46/1.85  tff(c_2126, plain, (![C_227, A_228]: (m1_pre_topc(g1_pre_topc(u1_struct_0(C_227), u1_pre_topc(C_227)), A_228) | ~m1_pre_topc(C_227, A_228) | ~l1_pre_topc(C_227) | ~v2_pre_topc(C_227) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_227), u1_pre_topc(C_227))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_227), u1_pre_topc(C_227))) | ~l1_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.46/1.85  tff(c_2138, plain, (![A_228]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_228) | ~m1_pre_topc('#skF_2', A_228) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_228))), inference(superposition, [status(thm), theory('equality')], [c_1843, c_2126])).
% 4.46/1.85  tff(c_2149, plain, (![A_229]: (m1_pre_topc('#skF_3', A_229) | ~m1_pre_topc('#skF_2', A_229) | ~l1_pre_topc(A_229))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2032, c_2018, c_1843, c_28, c_2032, c_2018, c_1843, c_34, c_32, c_2032, c_2018, c_2138])).
% 4.46/1.85  tff(c_2155, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1700, c_2149])).
% 4.46/1.85  tff(c_2159, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2155])).
% 4.46/1.85  tff(c_1698, plain, (v1_tsep_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 4.46/1.85  tff(c_1887, plain, (![B_209, A_210]: (v3_pre_topc(u1_struct_0(B_209), A_210) | ~v1_tsep_1(B_209, A_210) | ~m1_subset_1(u1_struct_0(B_209), k1_zfmisc_1(u1_struct_0(A_210))) | ~m1_pre_topc(B_209, A_210) | ~l1_pre_topc(A_210) | ~v2_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.46/1.85  tff(c_2215, plain, (![B_236, A_237]: (v3_pre_topc(u1_struct_0(B_236), A_237) | ~v1_tsep_1(B_236, A_237) | ~v2_pre_topc(A_237) | ~m1_pre_topc(B_236, A_237) | ~l1_pre_topc(A_237))), inference(resolution, [status(thm)], [c_24, c_1887])).
% 4.46/1.85  tff(c_2243, plain, (![A_239]: (v3_pre_topc(u1_struct_0('#skF_3'), A_239) | ~v1_tsep_1('#skF_2', A_239) | ~v2_pre_topc(A_239) | ~m1_pre_topc('#skF_2', A_239) | ~l1_pre_topc(A_239))), inference(superposition, [status(thm), theory('equality')], [c_1843, c_2215])).
% 4.46/1.85  tff(c_1953, plain, (![B_215, A_216]: (v1_tsep_1(B_215, A_216) | ~v3_pre_topc(u1_struct_0(B_215), A_216) | ~m1_subset_1(u1_struct_0(B_215), k1_zfmisc_1(u1_struct_0(A_216))) | ~m1_pre_topc(B_215, A_216) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.46/1.85  tff(c_1966, plain, (![B_26, A_24]: (v1_tsep_1(B_26, A_24) | ~v3_pre_topc(u1_struct_0(B_26), A_24) | ~v2_pre_topc(A_24) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_24, c_1953])).
% 4.46/1.85  tff(c_2402, plain, (![A_255]: (v1_tsep_1('#skF_3', A_255) | ~m1_pre_topc('#skF_3', A_255) | ~v1_tsep_1('#skF_2', A_255) | ~v2_pre_topc(A_255) | ~m1_pre_topc('#skF_2', A_255) | ~l1_pre_topc(A_255))), inference(resolution, [status(thm)], [c_2243, c_1966])).
% 4.46/1.85  tff(c_2408, plain, (v1_tsep_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1698, c_2402])).
% 4.46/1.85  tff(c_2412, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1700, c_38, c_2159, c_2408])).
% 4.46/1.85  tff(c_2414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1699, c_2412])).
% 4.46/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.85  
% 4.46/1.85  Inference rules
% 4.46/1.85  ----------------------
% 4.46/1.85  #Ref     : 14
% 4.46/1.85  #Sup     : 483
% 4.46/1.85  #Fact    : 0
% 4.46/1.85  #Define  : 0
% 4.46/1.85  #Split   : 16
% 4.46/1.85  #Chain   : 0
% 4.46/1.85  #Close   : 0
% 4.46/1.85  
% 4.46/1.85  Ordering : KBO
% 4.46/1.85  
% 4.46/1.85  Simplification rules
% 4.46/1.85  ----------------------
% 4.46/1.85  #Subsume      : 118
% 4.46/1.85  #Demod        : 701
% 4.46/1.85  #Tautology    : 223
% 4.46/1.85  #SimpNegUnit  : 5
% 4.46/1.85  #BackRed      : 36
% 4.46/1.85  
% 4.46/1.85  #Partial instantiations: 0
% 4.46/1.85  #Strategies tried      : 1
% 4.46/1.85  
% 4.46/1.85  Timing (in seconds)
% 4.46/1.85  ----------------------
% 4.46/1.85  Preprocessing        : 0.34
% 4.46/1.85  Parsing              : 0.17
% 4.46/1.85  CNF conversion       : 0.03
% 4.46/1.85  Main loop            : 0.70
% 4.46/1.85  Inferencing          : 0.25
% 4.46/1.86  Reduction            : 0.23
% 4.46/1.86  Demodulation         : 0.16
% 4.46/1.86  BG Simplification    : 0.03
% 4.46/1.86  Subsumption          : 0.13
% 4.46/1.86  Abstraction          : 0.03
% 4.46/1.86  MUC search           : 0.00
% 4.46/1.86  Cooper               : 0.00
% 4.46/1.86  Total                : 1.10
% 4.46/1.86  Index Insertion      : 0.00
% 4.46/1.86  Index Deletion       : 0.00
% 4.46/1.86  Index Matching       : 0.00
% 4.46/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
