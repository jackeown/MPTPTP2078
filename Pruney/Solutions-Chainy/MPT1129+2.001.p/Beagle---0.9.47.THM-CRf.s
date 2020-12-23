%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:10 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :  263 (1762 expanded)
%              Number of leaves         :   22 ( 520 expanded)
%              Depth                    :   17
%              Number of atoms          :  541 (4961 expanded)
%              Number of equality atoms :  115 ( 525 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v3_pre_topc(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
          <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_17] :
      ( m1_subset_1(u1_pre_topc(A_17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17))))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( l1_pre_topc(g1_pre_topc(A_5,B_6))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    ! [A_17] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_17),u1_pre_topc(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_40,c_8])).

tff(c_32,plain,
    ( v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_69,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_52,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_90,plain,(
    ! [B_31,A_32] :
      ( r2_hidden(B_31,u1_pre_topc(A_32))
      | ~ v3_pre_topc(B_31,A_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_93,plain,
    ( r2_hidden('#skF_3',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_69,c_90])).

tff(c_96,plain,(
    r2_hidden('#skF_3',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52,c_93])).

tff(c_12,plain,(
    ! [A_7] :
      ( m1_subset_1(u1_pre_topc(A_7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ! [A_19,B_20] :
      ( v1_pre_topc(g1_pre_topc(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [A_7] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_7),u1_pre_topc(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [D_23,B_24,C_25,A_26] :
      ( D_23 = B_24
      | g1_pre_topc(C_25,D_23) != g1_pre_topc(A_26,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_77,plain,(
    ! [A_1,B_24,A_26] :
      ( u1_pre_topc(A_1) = B_24
      | g1_pre_topc(A_26,B_24) != A_1
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_26)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_147,plain,(
    ! [A_47,B_48] :
      ( u1_pre_topc(g1_pre_topc(A_47,B_48)) = B_48
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_47)))
      | ~ v1_pre_topc(g1_pre_topc(A_47,B_48))
      | ~ l1_pre_topc(g1_pre_topc(A_47,B_48)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_77])).

tff(c_157,plain,(
    ! [A_51] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_51),u1_pre_topc(A_51))) = u1_pre_topc(A_51)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_51),u1_pre_topc(A_51)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_51),u1_pre_topc(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_12,c_147])).

tff(c_165,plain,(
    ! [A_52] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_52),u1_pre_topc(A_52))) = u1_pre_topc(A_52)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_52),u1_pre_topc(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_50,c_157])).

tff(c_172,plain,(
    ! [A_17] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_17),u1_pre_topc(A_17))) = u1_pre_topc(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_44,c_165])).

tff(c_84,plain,(
    ! [C_27,A_28,D_29,B_30] :
      ( C_27 = A_28
      | g1_pre_topc(C_27,D_29) != g1_pre_topc(A_28,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86,plain,(
    ! [A_1,A_28,B_30] :
      ( u1_struct_0(A_1) = A_28
      | g1_pre_topc(A_28,B_30) != A_1
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_28)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_152,plain,(
    ! [A_49,B_50] :
      ( u1_struct_0(g1_pre_topc(A_49,B_50)) = A_49
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49)))
      | ~ v1_pre_topc(g1_pre_topc(A_49,B_50))
      | ~ l1_pre_topc(g1_pre_topc(A_49,B_50)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_86])).

tff(c_250,plain,(
    ! [A_57] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_57),u1_pre_topc(A_57))) = u1_struct_0(A_57)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_57),u1_pre_topc(A_57)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_57),u1_pre_topc(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_12,c_152])).

tff(c_261,plain,(
    ! [A_58] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_58),u1_pre_topc(A_58))) = u1_struct_0(A_58)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_58),u1_pre_topc(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_50,c_250])).

tff(c_272,plain,(
    ! [A_59] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_59),u1_pre_topc(A_59))) = u1_struct_0(A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_44,c_261])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( v3_pre_topc(B_4,A_2)
      | ~ r2_hidden(B_4,u1_pre_topc(A_2))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1052,plain,(
    ! [B_81,A_82] :
      ( v3_pre_topc(B_81,g1_pre_topc(u1_struct_0(A_82),u1_pre_topc(A_82)))
      | ~ r2_hidden(B_81,u1_pre_topc(g1_pre_topc(u1_struct_0(A_82),u1_pre_topc(A_82))))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_82),u1_pre_topc(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_4])).

tff(c_1081,plain,(
    ! [B_83,A_84] :
      ( v3_pre_topc(B_83,g1_pre_topc(u1_struct_0(A_84),u1_pre_topc(A_84)))
      | ~ r2_hidden(B_83,u1_pre_topc(A_84))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_84),u1_pre_topc(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_1052])).

tff(c_26,plain,
    ( v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_141,plain,(
    ~ v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_1087,plain,
    ( ~ r2_hidden('#skF_3',u1_pre_topc('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1081,c_141])).

tff(c_1112,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_69,c_96,c_1087])).

tff(c_1118,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1112])).

tff(c_1124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1118])).

tff(c_1126,plain,(
    v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1140,plain,(
    ! [A_85,B_86] :
      ( u1_struct_0(g1_pre_topc(A_85,B_86)) = A_85
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k1_zfmisc_1(A_85)))
      | ~ v1_pre_topc(g1_pre_topc(A_85,B_86))
      | ~ l1_pre_topc(g1_pre_topc(A_85,B_86)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_86])).

tff(c_1150,plain,(
    ! [A_89] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_89),u1_pre_topc(A_89))) = u1_struct_0(A_89)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_89),u1_pre_topc(A_89)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_89),u1_pre_topc(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_12,c_1140])).

tff(c_1158,plain,(
    ! [A_90] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_90),u1_pre_topc(A_90))) = u1_struct_0(A_90)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_90),u1_pre_topc(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_50,c_1150])).

tff(c_1166,plain,(
    ! [A_91] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91))) = u1_struct_0(A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_44,c_1158])).

tff(c_1125,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1132,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitLeft,[status(thm)],[c_1125])).

tff(c_1175,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1166,c_1132])).

tff(c_1206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_69,c_1175])).

tff(c_1208,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(splitRight,[status(thm)],[c_1125])).

tff(c_22,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1232,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1126,c_1208,c_22])).

tff(c_1233,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1232])).

tff(c_6,plain,(
    ! [B_4,A_2] :
      ( r2_hidden(B_4,u1_pre_topc(A_2))
      | ~ v3_pre_topc(B_4,A_2)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1220,plain,
    ( r2_hidden('#skF_3',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1208,c_6])).

tff(c_1228,plain,
    ( r2_hidden('#skF_3',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1126,c_1220])).

tff(c_1234,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1228])).

tff(c_1240,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1234])).

tff(c_1246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1240])).

tff(c_1248,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1228])).

tff(c_1283,plain,(
    ! [A_92,B_93] :
      ( u1_pre_topc(g1_pre_topc(A_92,B_93)) = B_93
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92)))
      | ~ v1_pre_topc(g1_pre_topc(A_92,B_93))
      | ~ l1_pre_topc(g1_pre_topc(A_92,B_93)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_77])).

tff(c_1293,plain,(
    ! [A_96] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_96),u1_pre_topc(A_96))) = u1_pre_topc(A_96)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_96),u1_pre_topc(A_96)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_96),u1_pre_topc(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_12,c_1283])).

tff(c_1301,plain,(
    ! [A_97] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_97),u1_pre_topc(A_97))) = u1_pre_topc(A_97)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_97),u1_pre_topc(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_50,c_1293])).

tff(c_1304,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1248,c_1301])).

tff(c_1313,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1304])).

tff(c_1207,plain,(
    v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1125])).

tff(c_24,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v3_pre_topc('#skF_3',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1260,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1126,c_1208,c_24])).

tff(c_1266,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1260,c_6])).

tff(c_1275,plain,(
    r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_1207,c_1266])).

tff(c_1315,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_1275])).

tff(c_1324,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1313,c_2])).

tff(c_1342,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_1324])).

tff(c_1495,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1342])).

tff(c_1501,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1495])).

tff(c_1507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1501])).

tff(c_1509,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1342])).

tff(c_88,plain,(
    ! [A_1,C_27,D_29] :
      ( u1_struct_0(A_1) = C_27
      | g1_pre_topc(C_27,D_29) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_1405,plain,(
    ! [C_99,D_100] :
      ( u1_struct_0(g1_pre_topc(C_99,D_100)) = C_99
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_99,D_100)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_99,D_100)))))
      | ~ v1_pre_topc(g1_pre_topc(C_99,D_100))
      | ~ l1_pre_topc(g1_pre_topc(C_99,D_100)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_88])).

tff(c_1517,plain,(
    ! [C_101,D_102] :
      ( u1_struct_0(g1_pre_topc(C_101,D_102)) = C_101
      | ~ v1_pre_topc(g1_pre_topc(C_101,D_102))
      | ~ l1_pre_topc(g1_pre_topc(C_101,D_102)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1405])).

tff(c_1520,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1509,c_1517])).

tff(c_1532,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_1520])).

tff(c_1541,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1260])).

tff(c_1617,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1541,c_4])).

tff(c_1623,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1315,c_1617])).

tff(c_1625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1233,c_1623])).

tff(c_1626,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1232])).

tff(c_1647,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1228])).

tff(c_1653,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1647])).

tff(c_1659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1653])).

tff(c_1661,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1228])).

tff(c_1679,plain,(
    ! [A_105,B_106] :
      ( u1_pre_topc(g1_pre_topc(A_105,B_106)) = B_106
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(A_105)))
      | ~ v1_pre_topc(g1_pre_topc(A_105,B_106))
      | ~ l1_pre_topc(g1_pre_topc(A_105,B_106)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_77])).

tff(c_1689,plain,(
    ! [A_109] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_109),u1_pre_topc(A_109))) = u1_pre_topc(A_109)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_109),u1_pre_topc(A_109)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_109),u1_pre_topc(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_12,c_1679])).

tff(c_1697,plain,(
    ! [A_110] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_110),u1_pre_topc(A_110))) = u1_pre_topc(A_110)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_110),u1_pre_topc(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_50,c_1689])).

tff(c_1700,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1661,c_1697])).

tff(c_1709,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1700])).

tff(c_1720,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1709,c_2])).

tff(c_1738,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1661,c_1720])).

tff(c_1906,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1738])).

tff(c_1912,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1906])).

tff(c_1918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1912])).

tff(c_1920,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1738])).

tff(c_1729,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1709,c_12])).

tff(c_1744,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1661,c_1729])).

tff(c_1995,plain,(
    ! [C_118,D_119] :
      ( u1_struct_0(g1_pre_topc(C_118,D_119)) = C_118
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_118,D_119)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_118,D_119)))))
      | ~ v1_pre_topc(g1_pre_topc(C_118,D_119))
      | ~ l1_pre_topc(g1_pre_topc(C_118,D_119)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_88])).

tff(c_2007,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1709,c_1995])).

tff(c_2022,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1661,c_1920,c_1744,c_2007])).

tff(c_1629,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1126,c_1208,c_24])).

tff(c_2026,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_1629])).

tff(c_2029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1626,c_2026])).

tff(c_2031,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_28,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2048,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2031,c_28])).

tff(c_2049,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2048])).

tff(c_2030,plain,(
    v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2061,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_2031,c_30])).

tff(c_2067,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2061,c_6])).

tff(c_2075,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2030,c_2067])).

tff(c_2079,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2075])).

tff(c_2085,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2079])).

tff(c_2091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2085])).

tff(c_2093,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2075])).

tff(c_2054,plain,(
    ! [C_124,A_125,D_126,B_127] :
      ( C_124 = A_125
      | g1_pre_topc(C_124,D_126) != g1_pre_topc(A_125,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k1_zfmisc_1(A_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2056,plain,(
    ! [A_1,A_125,B_127] :
      ( u1_struct_0(A_1) = A_125
      | g1_pre_topc(A_125,B_127) != A_1
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k1_zfmisc_1(A_125)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2054])).

tff(c_2141,plain,(
    ! [A_144,B_145] :
      ( u1_struct_0(g1_pre_topc(A_144,B_145)) = A_144
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k1_zfmisc_1(A_144)))
      | ~ v1_pre_topc(g1_pre_topc(A_144,B_145))
      | ~ l1_pre_topc(g1_pre_topc(A_144,B_145)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2056])).

tff(c_2151,plain,(
    ! [A_148] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_148),u1_pre_topc(A_148))) = u1_struct_0(A_148)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_148),u1_pre_topc(A_148)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_148),u1_pre_topc(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_12,c_2141])).

tff(c_2159,plain,(
    ! [A_149] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_149),u1_pre_topc(A_149))) = u1_struct_0(A_149)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_149),u1_pre_topc(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(resolution,[status(thm)],[c_50,c_2151])).

tff(c_2162,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2093,c_2159])).

tff(c_2171,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2162])).

tff(c_2173,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2171,c_2061])).

tff(c_2236,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2173,c_4])).

tff(c_2242,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2236])).

tff(c_2243,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_2049,c_2242])).

tff(c_2195,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2171,c_12])).

tff(c_2214,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2093,c_2195])).

tff(c_2043,plain,(
    ! [D_120,B_121,C_122,A_123] :
      ( D_120 = B_121
      | g1_pre_topc(C_122,D_120) != g1_pre_topc(A_123,B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k1_zfmisc_1(A_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2047,plain,(
    ! [A_1,D_120,C_122] :
      ( u1_pre_topc(A_1) = D_120
      | g1_pre_topc(C_122,D_120) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2043])).

tff(c_2405,plain,(
    ! [C_155,D_156] :
      ( u1_pre_topc(g1_pre_topc(C_155,D_156)) = D_156
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_155,D_156)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_155,D_156)))))
      | ~ v1_pre_topc(g1_pre_topc(C_155,D_156))
      | ~ l1_pre_topc(g1_pre_topc(C_155,D_156)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2047])).

tff(c_2414,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2171,c_2405])).

tff(c_2427,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2093,c_2214,c_2414])).

tff(c_2443,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2427])).

tff(c_2449,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2443])).

tff(c_2455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2449])).

tff(c_2456,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2427])).

tff(c_2092,plain,(
    r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_2075])).

tff(c_2487,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_2092])).

tff(c_2492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2243,c_2487])).

tff(c_2493,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2048])).

tff(c_2506,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_2031,c_30])).

tff(c_2509,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2506,c_6])).

tff(c_2518,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2030,c_2509])).

tff(c_2524,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2518])).

tff(c_2531,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2524])).

tff(c_2537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2531])).

tff(c_2539,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2518])).

tff(c_2045,plain,(
    ! [A_1,B_121,A_123] :
      ( u1_pre_topc(A_1) = B_121
      | g1_pre_topc(A_123,B_121) != A_1
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k1_zfmisc_1(A_123)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2043])).

tff(c_2585,plain,(
    ! [A_180,B_181] :
      ( u1_pre_topc(g1_pre_topc(A_180,B_181)) = B_181
      | ~ m1_subset_1(B_181,k1_zfmisc_1(k1_zfmisc_1(A_180)))
      | ~ v1_pre_topc(g1_pre_topc(A_180,B_181))
      | ~ l1_pre_topc(g1_pre_topc(A_180,B_181)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2045])).

tff(c_2597,plain,(
    ! [A_184] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_184),u1_pre_topc(A_184))) = u1_pre_topc(A_184)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_184),u1_pre_topc(A_184)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_184),u1_pre_topc(A_184)))
      | ~ l1_pre_topc(A_184) ) ),
    inference(resolution,[status(thm)],[c_12,c_2585])).

tff(c_2605,plain,(
    ! [A_185] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_185),u1_pre_topc(A_185))) = u1_pre_topc(A_185)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_185),u1_pre_topc(A_185)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(resolution,[status(thm)],[c_50,c_2597])).

tff(c_2608,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2539,c_2605])).

tff(c_2617,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2608])).

tff(c_2635,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2617,c_12])).

tff(c_2650,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2539,c_2635])).

tff(c_2499,plain,(
    ! [C_160,A_161,D_162,B_163] :
      ( C_160 = A_161
      | g1_pre_topc(C_160,D_162) != g1_pre_topc(A_161,B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(k1_zfmisc_1(A_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2503,plain,(
    ! [A_1,C_160,D_162] :
      ( u1_struct_0(A_1) = C_160
      | g1_pre_topc(C_160,D_162) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2499])).

tff(c_2812,plain,(
    ! [C_187,D_188] :
      ( u1_struct_0(g1_pre_topc(C_187,D_188)) = C_187
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_187,D_188)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_187,D_188)))))
      | ~ v1_pre_topc(g1_pre_topc(C_187,D_188))
      | ~ l1_pre_topc(g1_pre_topc(C_187,D_188)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2503])).

tff(c_2821,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2617,c_2812])).

tff(c_2834,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2539,c_2650,c_2821])).

tff(c_2856,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2834])).

tff(c_2862,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2856])).

tff(c_2868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2862])).

tff(c_2869,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2834])).

tff(c_2908,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2869,c_2506])).

tff(c_2915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2493,c_2908])).

tff(c_2917,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2939,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2917,c_34])).

tff(c_2940,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2939])).

tff(c_2916,plain,(
    v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2942,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_2917,c_36])).

tff(c_2966,plain,(
    ! [B_200,A_201] :
      ( r2_hidden(B_200,u1_pre_topc(A_201))
      | ~ v3_pre_topc(B_200,A_201)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2969,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2942,c_2966])).

tff(c_2972,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2916,c_2969])).

tff(c_2980,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2972])).

tff(c_2986,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2980])).

tff(c_2992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2986])).

tff(c_2994,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2972])).

tff(c_2952,plain,(
    ! [C_192,A_193,D_194,B_195] :
      ( C_192 = A_193
      | g1_pre_topc(C_192,D_194) != g1_pre_topc(A_193,B_195)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(k1_zfmisc_1(A_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2954,plain,(
    ! [A_1,A_193,B_195] :
      ( u1_struct_0(A_1) = A_193
      | g1_pre_topc(A_193,B_195) != A_1
      | ~ m1_subset_1(B_195,k1_zfmisc_1(k1_zfmisc_1(A_193)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2952])).

tff(c_3042,plain,(
    ! [A_216,B_217] :
      ( u1_struct_0(g1_pre_topc(A_216,B_217)) = A_216
      | ~ m1_subset_1(B_217,k1_zfmisc_1(k1_zfmisc_1(A_216)))
      | ~ v1_pre_topc(g1_pre_topc(A_216,B_217))
      | ~ l1_pre_topc(g1_pre_topc(A_216,B_217)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2954])).

tff(c_3052,plain,(
    ! [A_220] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_220),u1_pre_topc(A_220))) = u1_struct_0(A_220)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_220),u1_pre_topc(A_220)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_220),u1_pre_topc(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(resolution,[status(thm)],[c_12,c_3042])).

tff(c_3060,plain,(
    ! [A_221] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_221),u1_pre_topc(A_221))) = u1_struct_0(A_221)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_221),u1_pre_topc(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(resolution,[status(thm)],[c_50,c_3052])).

tff(c_3063,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2994,c_3060])).

tff(c_3072,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3063])).

tff(c_3074,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3072,c_2942])).

tff(c_3123,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3074,c_4])).

tff(c_3129,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3123])).

tff(c_3130,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_2940,c_3129])).

tff(c_3096,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3072,c_12])).

tff(c_3115,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_3096])).

tff(c_2961,plain,(
    ! [D_196,B_197,C_198,A_199] :
      ( D_196 = B_197
      | g1_pre_topc(C_198,D_196) != g1_pre_topc(A_199,B_197)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k1_zfmisc_1(A_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2965,plain,(
    ! [A_1,D_196,C_198] :
      ( u1_pre_topc(A_1) = D_196
      | g1_pre_topc(C_198,D_196) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2961])).

tff(c_3436,plain,(
    ! [C_229,D_230] :
      ( u1_pre_topc(g1_pre_topc(C_229,D_230)) = D_230
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_229,D_230)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_229,D_230)))))
      | ~ v1_pre_topc(g1_pre_topc(C_229,D_230))
      | ~ l1_pre_topc(g1_pre_topc(C_229,D_230)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2965])).

tff(c_3448,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3072,c_3436])).

tff(c_3463,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_3115,c_3448])).

tff(c_3479,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3463])).

tff(c_3485,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_3479])).

tff(c_3491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3485])).

tff(c_3492,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3463])).

tff(c_2993,plain,(
    r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_2972])).

tff(c_3529,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3492,c_2993])).

tff(c_3534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3130,c_3529])).

tff(c_3535,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2939])).

tff(c_3538,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_2917,c_36])).

tff(c_3565,plain,(
    ! [B_242,A_243] :
      ( r2_hidden(B_242,u1_pre_topc(A_243))
      | ~ v3_pre_topc(B_242,A_243)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3568,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v3_pre_topc('#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_3538,c_3565])).

tff(c_3571,plain,
    ( r2_hidden('#skF_2',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2916,c_3568])).

tff(c_3579,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3571])).

tff(c_3585,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_3579])).

tff(c_3591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3585])).

tff(c_3593,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_3571])).

tff(c_3549,plain,(
    ! [D_234,B_235,C_236,A_237] :
      ( D_234 = B_235
      | g1_pre_topc(C_236,D_234) != g1_pre_topc(A_237,B_235)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(k1_zfmisc_1(A_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3551,plain,(
    ! [A_1,B_235,A_237] :
      ( u1_pre_topc(A_1) = B_235
      | g1_pre_topc(A_237,B_235) != A_1
      | ~ m1_subset_1(B_235,k1_zfmisc_1(k1_zfmisc_1(A_237)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3549])).

tff(c_3643,plain,(
    ! [A_258,B_259] :
      ( u1_pre_topc(g1_pre_topc(A_258,B_259)) = B_259
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k1_zfmisc_1(A_258)))
      | ~ v1_pre_topc(g1_pre_topc(A_258,B_259))
      | ~ l1_pre_topc(g1_pre_topc(A_258,B_259)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3551])).

tff(c_3654,plain,(
    ! [A_262] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_262),u1_pre_topc(A_262))) = u1_pre_topc(A_262)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(A_262),u1_pre_topc(A_262)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_262),u1_pre_topc(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(resolution,[status(thm)],[c_12,c_3643])).

tff(c_3662,plain,(
    ! [A_263] :
      ( u1_pre_topc(g1_pre_topc(u1_struct_0(A_263),u1_pre_topc(A_263))) = u1_pre_topc(A_263)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_263),u1_pre_topc(A_263)))
      | ~ l1_pre_topc(A_263) ) ),
    inference(resolution,[status(thm)],[c_50,c_3654])).

tff(c_3665,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3593,c_3662])).

tff(c_3674,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3665])).

tff(c_3683,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3674,c_2])).

tff(c_3701,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_pre_topc('#skF_1')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3593,c_3683])).

tff(c_3878,plain,(
    ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3701])).

tff(c_3884,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_3878])).

tff(c_3890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3884])).

tff(c_3892,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_3701])).

tff(c_3692,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3674,c_12])).

tff(c_3707,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3593,c_3692])).

tff(c_3558,plain,(
    ! [C_238,A_239,D_240,B_241] :
      ( C_238 = A_239
      | g1_pre_topc(C_238,D_240) != g1_pre_topc(A_239,B_241)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(k1_zfmisc_1(A_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3562,plain,(
    ! [A_1,C_238,D_240] :
      ( u1_struct_0(A_1) = C_238
      | g1_pre_topc(C_238,D_240) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3558])).

tff(c_3969,plain,(
    ! [C_271,D_272] :
      ( u1_struct_0(g1_pre_topc(C_271,D_272)) = C_271
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(C_271,D_272)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_271,D_272)))))
      | ~ v1_pre_topc(g1_pre_topc(C_271,D_272))
      | ~ l1_pre_topc(g1_pre_topc(C_271,D_272)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3562])).

tff(c_3981,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3674,c_3969])).

tff(c_3996,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3593,c_3892,c_3707,c_3981])).

tff(c_4000,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3996,c_3538])).

tff(c_4002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3535,c_4000])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:54:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.14  
% 5.77/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.14  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.77/2.14  
% 5.77/2.14  %Foreground sorts:
% 5.77/2.14  
% 5.77/2.14  
% 5.77/2.14  %Background operators:
% 5.77/2.14  
% 5.77/2.14  
% 5.77/2.14  %Foreground operators:
% 5.77/2.14  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.77/2.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.77/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.77/2.14  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.77/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.77/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.77/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.77/2.14  tff('#skF_3', type, '#skF_3': $i).
% 5.77/2.14  tff('#skF_1', type, '#skF_1': $i).
% 5.77/2.14  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.77/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.77/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.77/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.77/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.77/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.77/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.77/2.14  
% 5.88/2.17  tff(f_73, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 5.88/2.17  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 5.88/2.17  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 5.88/2.17  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 5.88/2.17  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 5.88/2.17  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 5.88/2.17  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.17  tff(c_40, plain, (![A_17]: (m1_subset_1(u1_pre_topc(A_17), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17)))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.88/2.17  tff(c_8, plain, (![A_5, B_6]: (l1_pre_topc(g1_pre_topc(A_5, B_6)) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.88/2.17  tff(c_44, plain, (![A_17]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_17), u1_pre_topc(A_17))) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_40, c_8])).
% 5.88/2.17  tff(c_32, plain, (v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.17  tff(c_69, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_32])).
% 5.88/2.17  tff(c_38, plain, (v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.17  tff(c_52, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 5.88/2.17  tff(c_90, plain, (![B_31, A_32]: (r2_hidden(B_31, u1_pre_topc(A_32)) | ~v3_pre_topc(B_31, A_32) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.88/2.17  tff(c_93, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_69, c_90])).
% 5.88/2.17  tff(c_96, plain, (r2_hidden('#skF_3', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_52, c_93])).
% 5.88/2.17  tff(c_12, plain, (![A_7]: (m1_subset_1(u1_pre_topc(A_7), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7)))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.88/2.17  tff(c_46, plain, (![A_19, B_20]: (v1_pre_topc(g1_pre_topc(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.88/2.17  tff(c_50, plain, (![A_7]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_7), u1_pre_topc(A_7))) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_12, c_46])).
% 5.88/2.17  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.88/2.17  tff(c_75, plain, (![D_23, B_24, C_25, A_26]: (D_23=B_24 | g1_pre_topc(C_25, D_23)!=g1_pre_topc(A_26, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.88/2.17  tff(c_77, plain, (![A_1, B_24, A_26]: (u1_pre_topc(A_1)=B_24 | g1_pre_topc(A_26, B_24)!=A_1 | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_26))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 5.88/2.17  tff(c_147, plain, (![A_47, B_48]: (u1_pre_topc(g1_pre_topc(A_47, B_48))=B_48 | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(A_47))) | ~v1_pre_topc(g1_pre_topc(A_47, B_48)) | ~l1_pre_topc(g1_pre_topc(A_47, B_48)))), inference(reflexivity, [status(thm), theory('equality')], [c_77])).
% 5.88/2.17  tff(c_157, plain, (![A_51]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_51), u1_pre_topc(A_51)))=u1_pre_topc(A_51) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_51), u1_pre_topc(A_51))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_51), u1_pre_topc(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_12, c_147])).
% 5.88/2.17  tff(c_165, plain, (![A_52]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_52), u1_pre_topc(A_52)))=u1_pre_topc(A_52) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_52), u1_pre_topc(A_52))) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_50, c_157])).
% 5.88/2.17  tff(c_172, plain, (![A_17]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_17), u1_pre_topc(A_17)))=u1_pre_topc(A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_44, c_165])).
% 5.88/2.17  tff(c_84, plain, (![C_27, A_28, D_29, B_30]: (C_27=A_28 | g1_pre_topc(C_27, D_29)!=g1_pre_topc(A_28, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_28))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.88/2.17  tff(c_86, plain, (![A_1, A_28, B_30]: (u1_struct_0(A_1)=A_28 | g1_pre_topc(A_28, B_30)!=A_1 | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_28))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_84])).
% 5.88/2.17  tff(c_152, plain, (![A_49, B_50]: (u1_struct_0(g1_pre_topc(A_49, B_50))=A_49 | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))) | ~v1_pre_topc(g1_pre_topc(A_49, B_50)) | ~l1_pre_topc(g1_pre_topc(A_49, B_50)))), inference(reflexivity, [status(thm), theory('equality')], [c_86])).
% 5.88/2.17  tff(c_250, plain, (![A_57]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_57), u1_pre_topc(A_57)))=u1_struct_0(A_57) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_57), u1_pre_topc(A_57))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_57), u1_pre_topc(A_57))) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_12, c_152])).
% 5.88/2.17  tff(c_261, plain, (![A_58]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_58), u1_pre_topc(A_58)))=u1_struct_0(A_58) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_58), u1_pre_topc(A_58))) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_50, c_250])).
% 5.88/2.17  tff(c_272, plain, (![A_59]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_59), u1_pre_topc(A_59)))=u1_struct_0(A_59) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_44, c_261])).
% 5.88/2.17  tff(c_4, plain, (![B_4, A_2]: (v3_pre_topc(B_4, A_2) | ~r2_hidden(B_4, u1_pre_topc(A_2)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.88/2.17  tff(c_1052, plain, (![B_81, A_82]: (v3_pre_topc(B_81, g1_pre_topc(u1_struct_0(A_82), u1_pre_topc(A_82))) | ~r2_hidden(B_81, u1_pre_topc(g1_pre_topc(u1_struct_0(A_82), u1_pre_topc(A_82)))) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_82), u1_pre_topc(A_82))) | ~l1_pre_topc(A_82))), inference(superposition, [status(thm), theory('equality')], [c_272, c_4])).
% 5.88/2.17  tff(c_1081, plain, (![B_83, A_84]: (v3_pre_topc(B_83, g1_pre_topc(u1_struct_0(A_84), u1_pre_topc(A_84))) | ~r2_hidden(B_83, u1_pre_topc(A_84)) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_84), u1_pre_topc(A_84))) | ~l1_pre_topc(A_84) | ~l1_pre_topc(A_84))), inference(superposition, [status(thm), theory('equality')], [c_172, c_1052])).
% 5.88/2.17  tff(c_26, plain, (v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v3_pre_topc('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.17  tff(c_141, plain, (~v3_pre_topc('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_26])).
% 5.88/2.17  tff(c_1087, plain, (~r2_hidden('#skF_3', u1_pre_topc('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1081, c_141])).
% 5.88/2.17  tff(c_1112, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_69, c_96, c_1087])).
% 5.88/2.17  tff(c_1118, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1112])).
% 5.88/2.17  tff(c_1124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1118])).
% 5.88/2.17  tff(c_1126, plain, (v3_pre_topc('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_26])).
% 5.88/2.17  tff(c_1140, plain, (![A_85, B_86]: (u1_struct_0(g1_pre_topc(A_85, B_86))=A_85 | ~m1_subset_1(B_86, k1_zfmisc_1(k1_zfmisc_1(A_85))) | ~v1_pre_topc(g1_pre_topc(A_85, B_86)) | ~l1_pre_topc(g1_pre_topc(A_85, B_86)))), inference(reflexivity, [status(thm), theory('equality')], [c_86])).
% 5.88/2.17  tff(c_1150, plain, (![A_89]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_89), u1_pre_topc(A_89)))=u1_struct_0(A_89) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_89), u1_pre_topc(A_89))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_89), u1_pre_topc(A_89))) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_12, c_1140])).
% 5.88/2.17  tff(c_1158, plain, (![A_90]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_90), u1_pre_topc(A_90)))=u1_struct_0(A_90) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_90), u1_pre_topc(A_90))) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_50, c_1150])).
% 5.88/2.17  tff(c_1166, plain, (![A_91]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91)))=u1_struct_0(A_91) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_44, c_1158])).
% 5.88/2.17  tff(c_1125, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_26])).
% 5.88/2.17  tff(c_1132, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitLeft, [status(thm)], [c_1125])).
% 5.88/2.17  tff(c_1175, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1166, c_1132])).
% 5.88/2.17  tff(c_1206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_69, c_1175])).
% 5.88/2.17  tff(c_1208, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(splitRight, [status(thm)], [c_1125])).
% 5.88/2.17  tff(c_22, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v3_pre_topc('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.17  tff(c_1232, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1126, c_1208, c_22])).
% 5.88/2.17  tff(c_1233, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1232])).
% 5.88/2.17  tff(c_6, plain, (![B_4, A_2]: (r2_hidden(B_4, u1_pre_topc(A_2)) | ~v3_pre_topc(B_4, A_2) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.88/2.17  tff(c_1220, plain, (r2_hidden('#skF_3', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v3_pre_topc('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_1208, c_6])).
% 5.88/2.17  tff(c_1228, plain, (r2_hidden('#skF_3', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1126, c_1220])).
% 5.88/2.17  tff(c_1234, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_1228])).
% 5.88/2.17  tff(c_1240, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1234])).
% 5.88/2.17  tff(c_1246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1240])).
% 5.88/2.17  tff(c_1248, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_1228])).
% 5.88/2.17  tff(c_1283, plain, (![A_92, B_93]: (u1_pre_topc(g1_pre_topc(A_92, B_93))=B_93 | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(A_92))) | ~v1_pre_topc(g1_pre_topc(A_92, B_93)) | ~l1_pre_topc(g1_pre_topc(A_92, B_93)))), inference(reflexivity, [status(thm), theory('equality')], [c_77])).
% 5.88/2.17  tff(c_1293, plain, (![A_96]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_96), u1_pre_topc(A_96)))=u1_pre_topc(A_96) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_96), u1_pre_topc(A_96))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_96), u1_pre_topc(A_96))) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_12, c_1283])).
% 5.88/2.17  tff(c_1301, plain, (![A_97]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_97), u1_pre_topc(A_97)))=u1_pre_topc(A_97) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_97), u1_pre_topc(A_97))) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_50, c_1293])).
% 5.88/2.17  tff(c_1304, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1248, c_1301])).
% 5.88/2.17  tff(c_1313, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1304])).
% 5.88/2.17  tff(c_1207, plain, (v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_1125])).
% 5.88/2.17  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v3_pre_topc('#skF_3', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.17  tff(c_1260, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_1126, c_1208, c_24])).
% 5.88/2.17  tff(c_1266, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_1260, c_6])).
% 5.88/2.17  tff(c_1275, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_1207, c_1266])).
% 5.88/2.17  tff(c_1315, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_1275])).
% 5.88/2.17  tff(c_1324, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1313, c_2])).
% 5.88/2.17  tff(c_1342, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_1324])).
% 5.88/2.17  tff(c_1495, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_1342])).
% 5.88/2.17  tff(c_1501, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1495])).
% 5.88/2.17  tff(c_1507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1501])).
% 5.88/2.17  tff(c_1509, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_1342])).
% 5.88/2.17  tff(c_88, plain, (![A_1, C_27, D_29]: (u1_struct_0(A_1)=C_27 | g1_pre_topc(C_27, D_29)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_84])).
% 5.88/2.17  tff(c_1405, plain, (![C_99, D_100]: (u1_struct_0(g1_pre_topc(C_99, D_100))=C_99 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_99, D_100)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_99, D_100))))) | ~v1_pre_topc(g1_pre_topc(C_99, D_100)) | ~l1_pre_topc(g1_pre_topc(C_99, D_100)))), inference(reflexivity, [status(thm), theory('equality')], [c_88])).
% 5.88/2.17  tff(c_1517, plain, (![C_101, D_102]: (u1_struct_0(g1_pre_topc(C_101, D_102))=C_101 | ~v1_pre_topc(g1_pre_topc(C_101, D_102)) | ~l1_pre_topc(g1_pre_topc(C_101, D_102)))), inference(resolution, [status(thm)], [c_12, c_1405])).
% 5.88/2.17  tff(c_1520, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_1509, c_1517])).
% 5.88/2.17  tff(c_1532, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_1520])).
% 5.88/2.17  tff(c_1541, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_1260])).
% 5.88/2.17  tff(c_1617, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1541, c_4])).
% 5.88/2.17  tff(c_1623, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1315, c_1617])).
% 5.88/2.17  tff(c_1625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1233, c_1623])).
% 5.88/2.17  tff(c_1626, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1232])).
% 5.88/2.17  tff(c_1647, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_1228])).
% 5.88/2.17  tff(c_1653, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1647])).
% 5.88/2.17  tff(c_1659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1653])).
% 5.88/2.17  tff(c_1661, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_1228])).
% 5.88/2.17  tff(c_1679, plain, (![A_105, B_106]: (u1_pre_topc(g1_pre_topc(A_105, B_106))=B_106 | ~m1_subset_1(B_106, k1_zfmisc_1(k1_zfmisc_1(A_105))) | ~v1_pre_topc(g1_pre_topc(A_105, B_106)) | ~l1_pre_topc(g1_pre_topc(A_105, B_106)))), inference(reflexivity, [status(thm), theory('equality')], [c_77])).
% 5.88/2.17  tff(c_1689, plain, (![A_109]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_109), u1_pre_topc(A_109)))=u1_pre_topc(A_109) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_109), u1_pre_topc(A_109))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_109), u1_pre_topc(A_109))) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_12, c_1679])).
% 5.88/2.17  tff(c_1697, plain, (![A_110]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_110), u1_pre_topc(A_110)))=u1_pre_topc(A_110) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_110), u1_pre_topc(A_110))) | ~l1_pre_topc(A_110))), inference(resolution, [status(thm)], [c_50, c_1689])).
% 5.88/2.17  tff(c_1700, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1661, c_1697])).
% 5.88/2.17  tff(c_1709, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1700])).
% 5.88/2.17  tff(c_1720, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1709, c_2])).
% 5.88/2.17  tff(c_1738, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1661, c_1720])).
% 5.88/2.17  tff(c_1906, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_1738])).
% 5.88/2.17  tff(c_1912, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1906])).
% 5.88/2.17  tff(c_1918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1912])).
% 5.88/2.17  tff(c_1920, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_1738])).
% 5.88/2.17  tff(c_1729, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1709, c_12])).
% 5.88/2.17  tff(c_1744, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_1661, c_1729])).
% 5.88/2.17  tff(c_1995, plain, (![C_118, D_119]: (u1_struct_0(g1_pre_topc(C_118, D_119))=C_118 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_118, D_119)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_118, D_119))))) | ~v1_pre_topc(g1_pre_topc(C_118, D_119)) | ~l1_pre_topc(g1_pre_topc(C_118, D_119)))), inference(reflexivity, [status(thm), theory('equality')], [c_88])).
% 5.88/2.17  tff(c_2007, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1709, c_1995])).
% 5.88/2.17  tff(c_2022, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1661, c_1920, c_1744, c_2007])).
% 5.88/2.17  tff(c_1629, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_1126, c_1208, c_24])).
% 5.88/2.17  tff(c_2026, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2022, c_1629])).
% 5.88/2.17  tff(c_2029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1626, c_2026])).
% 5.88/2.17  tff(c_2031, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_32])).
% 5.88/2.17  tff(c_28, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc('#skF_2', '#skF_1') | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.17  tff(c_2048, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2031, c_28])).
% 5.88/2.17  tff(c_2049, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_2048])).
% 5.88/2.17  tff(c_2030, plain, (v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_32])).
% 5.88/2.17  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.17  tff(c_2061, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_2031, c_30])).
% 5.88/2.17  tff(c_2067, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_2061, c_6])).
% 5.88/2.17  tff(c_2075, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2030, c_2067])).
% 5.88/2.17  tff(c_2079, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_2075])).
% 5.88/2.17  tff(c_2085, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2079])).
% 5.88/2.17  tff(c_2091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_2085])).
% 5.88/2.17  tff(c_2093, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_2075])).
% 5.88/2.17  tff(c_2054, plain, (![C_124, A_125, D_126, B_127]: (C_124=A_125 | g1_pre_topc(C_124, D_126)!=g1_pre_topc(A_125, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(k1_zfmisc_1(A_125))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.88/2.17  tff(c_2056, plain, (![A_1, A_125, B_127]: (u1_struct_0(A_1)=A_125 | g1_pre_topc(A_125, B_127)!=A_1 | ~m1_subset_1(B_127, k1_zfmisc_1(k1_zfmisc_1(A_125))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2054])).
% 5.88/2.17  tff(c_2141, plain, (![A_144, B_145]: (u1_struct_0(g1_pre_topc(A_144, B_145))=A_144 | ~m1_subset_1(B_145, k1_zfmisc_1(k1_zfmisc_1(A_144))) | ~v1_pre_topc(g1_pre_topc(A_144, B_145)) | ~l1_pre_topc(g1_pre_topc(A_144, B_145)))), inference(reflexivity, [status(thm), theory('equality')], [c_2056])).
% 5.88/2.17  tff(c_2151, plain, (![A_148]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_148), u1_pre_topc(A_148)))=u1_struct_0(A_148) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_148), u1_pre_topc(A_148))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_148), u1_pre_topc(A_148))) | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_12, c_2141])).
% 5.88/2.17  tff(c_2159, plain, (![A_149]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_149), u1_pre_topc(A_149)))=u1_struct_0(A_149) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_149), u1_pre_topc(A_149))) | ~l1_pre_topc(A_149))), inference(resolution, [status(thm)], [c_50, c_2151])).
% 5.88/2.17  tff(c_2162, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2093, c_2159])).
% 5.88/2.17  tff(c_2171, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2162])).
% 5.88/2.17  tff(c_2173, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2171, c_2061])).
% 5.88/2.17  tff(c_2236, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2173, c_4])).
% 5.88/2.17  tff(c_2242, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2236])).
% 5.88/2.17  tff(c_2243, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_2049, c_2242])).
% 5.88/2.17  tff(c_2195, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2171, c_12])).
% 5.88/2.17  tff(c_2214, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_2093, c_2195])).
% 5.88/2.17  tff(c_2043, plain, (![D_120, B_121, C_122, A_123]: (D_120=B_121 | g1_pre_topc(C_122, D_120)!=g1_pre_topc(A_123, B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(k1_zfmisc_1(A_123))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.88/2.17  tff(c_2047, plain, (![A_1, D_120, C_122]: (u1_pre_topc(A_1)=D_120 | g1_pre_topc(C_122, D_120)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2043])).
% 5.88/2.17  tff(c_2405, plain, (![C_155, D_156]: (u1_pre_topc(g1_pre_topc(C_155, D_156))=D_156 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_155, D_156)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_155, D_156))))) | ~v1_pre_topc(g1_pre_topc(C_155, D_156)) | ~l1_pre_topc(g1_pre_topc(C_155, D_156)))), inference(reflexivity, [status(thm), theory('equality')], [c_2047])).
% 5.88/2.17  tff(c_2414, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2171, c_2405])).
% 5.88/2.17  tff(c_2427, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2093, c_2214, c_2414])).
% 5.88/2.17  tff(c_2443, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_2427])).
% 5.88/2.17  tff(c_2449, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2443])).
% 5.88/2.17  tff(c_2455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_2449])).
% 5.88/2.17  tff(c_2456, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(splitRight, [status(thm)], [c_2427])).
% 5.88/2.17  tff(c_2092, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_2075])).
% 5.88/2.17  tff(c_2487, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_2092])).
% 5.88/2.17  tff(c_2492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2243, c_2487])).
% 5.88/2.17  tff(c_2493, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2048])).
% 5.88/2.17  tff(c_2506, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_2031, c_30])).
% 5.88/2.17  tff(c_2509, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_2506, c_6])).
% 5.88/2.17  tff(c_2518, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2030, c_2509])).
% 5.88/2.17  tff(c_2524, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_2518])).
% 5.88/2.17  tff(c_2531, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2524])).
% 5.88/2.17  tff(c_2537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_2531])).
% 5.88/2.17  tff(c_2539, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_2518])).
% 5.88/2.17  tff(c_2045, plain, (![A_1, B_121, A_123]: (u1_pre_topc(A_1)=B_121 | g1_pre_topc(A_123, B_121)!=A_1 | ~m1_subset_1(B_121, k1_zfmisc_1(k1_zfmisc_1(A_123))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2043])).
% 5.88/2.17  tff(c_2585, plain, (![A_180, B_181]: (u1_pre_topc(g1_pre_topc(A_180, B_181))=B_181 | ~m1_subset_1(B_181, k1_zfmisc_1(k1_zfmisc_1(A_180))) | ~v1_pre_topc(g1_pre_topc(A_180, B_181)) | ~l1_pre_topc(g1_pre_topc(A_180, B_181)))), inference(reflexivity, [status(thm), theory('equality')], [c_2045])).
% 5.88/2.17  tff(c_2597, plain, (![A_184]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_184), u1_pre_topc(A_184)))=u1_pre_topc(A_184) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_184), u1_pre_topc(A_184))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_184), u1_pre_topc(A_184))) | ~l1_pre_topc(A_184))), inference(resolution, [status(thm)], [c_12, c_2585])).
% 5.88/2.17  tff(c_2605, plain, (![A_185]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_185), u1_pre_topc(A_185)))=u1_pre_topc(A_185) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_185), u1_pre_topc(A_185))) | ~l1_pre_topc(A_185))), inference(resolution, [status(thm)], [c_50, c_2597])).
% 5.88/2.17  tff(c_2608, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2539, c_2605])).
% 5.88/2.17  tff(c_2617, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2608])).
% 5.88/2.17  tff(c_2635, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2617, c_12])).
% 5.88/2.17  tff(c_2650, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_2539, c_2635])).
% 5.88/2.17  tff(c_2499, plain, (![C_160, A_161, D_162, B_163]: (C_160=A_161 | g1_pre_topc(C_160, D_162)!=g1_pre_topc(A_161, B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(k1_zfmisc_1(A_161))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.88/2.17  tff(c_2503, plain, (![A_1, C_160, D_162]: (u1_struct_0(A_1)=C_160 | g1_pre_topc(C_160, D_162)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2499])).
% 5.88/2.17  tff(c_2812, plain, (![C_187, D_188]: (u1_struct_0(g1_pre_topc(C_187, D_188))=C_187 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_187, D_188)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_187, D_188))))) | ~v1_pre_topc(g1_pre_topc(C_187, D_188)) | ~l1_pre_topc(g1_pre_topc(C_187, D_188)))), inference(reflexivity, [status(thm), theory('equality')], [c_2503])).
% 5.88/2.17  tff(c_2821, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2617, c_2812])).
% 5.88/2.17  tff(c_2834, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2539, c_2650, c_2821])).
% 5.88/2.17  tff(c_2856, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_2834])).
% 5.88/2.17  tff(c_2862, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2856])).
% 5.88/2.17  tff(c_2868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_2862])).
% 5.88/2.17  tff(c_2869, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2834])).
% 5.88/2.17  tff(c_2908, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2869, c_2506])).
% 5.88/2.17  tff(c_2915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2493, c_2908])).
% 5.88/2.17  tff(c_2917, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 5.88/2.17  tff(c_34, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc('#skF_2', '#skF_1') | v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.17  tff(c_2939, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v3_pre_topc('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2917, c_34])).
% 5.88/2.17  tff(c_2940, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_2939])).
% 5.88/2.17  tff(c_2916, plain, (v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_38])).
% 5.88/2.17  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.88/2.17  tff(c_2942, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_2917, c_36])).
% 5.88/2.17  tff(c_2966, plain, (![B_200, A_201]: (r2_hidden(B_200, u1_pre_topc(A_201)) | ~v3_pre_topc(B_200, A_201) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.88/2.17  tff(c_2969, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_2942, c_2966])).
% 5.88/2.17  tff(c_2972, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2916, c_2969])).
% 5.88/2.17  tff(c_2980, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_2972])).
% 5.88/2.17  tff(c_2986, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2980])).
% 5.88/2.17  tff(c_2992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_2986])).
% 5.88/2.17  tff(c_2994, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_2972])).
% 5.88/2.17  tff(c_2952, plain, (![C_192, A_193, D_194, B_195]: (C_192=A_193 | g1_pre_topc(C_192, D_194)!=g1_pre_topc(A_193, B_195) | ~m1_subset_1(B_195, k1_zfmisc_1(k1_zfmisc_1(A_193))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.88/2.17  tff(c_2954, plain, (![A_1, A_193, B_195]: (u1_struct_0(A_1)=A_193 | g1_pre_topc(A_193, B_195)!=A_1 | ~m1_subset_1(B_195, k1_zfmisc_1(k1_zfmisc_1(A_193))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2952])).
% 5.88/2.17  tff(c_3042, plain, (![A_216, B_217]: (u1_struct_0(g1_pre_topc(A_216, B_217))=A_216 | ~m1_subset_1(B_217, k1_zfmisc_1(k1_zfmisc_1(A_216))) | ~v1_pre_topc(g1_pre_topc(A_216, B_217)) | ~l1_pre_topc(g1_pre_topc(A_216, B_217)))), inference(reflexivity, [status(thm), theory('equality')], [c_2954])).
% 5.88/2.17  tff(c_3052, plain, (![A_220]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_220), u1_pre_topc(A_220)))=u1_struct_0(A_220) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_220), u1_pre_topc(A_220))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_220), u1_pre_topc(A_220))) | ~l1_pre_topc(A_220))), inference(resolution, [status(thm)], [c_12, c_3042])).
% 5.88/2.17  tff(c_3060, plain, (![A_221]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_221), u1_pre_topc(A_221)))=u1_struct_0(A_221) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_221), u1_pre_topc(A_221))) | ~l1_pre_topc(A_221))), inference(resolution, [status(thm)], [c_50, c_3052])).
% 5.88/2.17  tff(c_3063, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2994, c_3060])).
% 5.88/2.17  tff(c_3072, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3063])).
% 5.88/2.17  tff(c_3074, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3072, c_2942])).
% 5.88/2.17  tff(c_3123, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3074, c_4])).
% 5.88/2.17  tff(c_3129, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3123])).
% 5.88/2.17  tff(c_3130, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_2940, c_3129])).
% 5.88/2.17  tff(c_3096, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3072, c_12])).
% 5.88/2.17  tff(c_3115, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_3096])).
% 5.88/2.17  tff(c_2961, plain, (![D_196, B_197, C_198, A_199]: (D_196=B_197 | g1_pre_topc(C_198, D_196)!=g1_pre_topc(A_199, B_197) | ~m1_subset_1(B_197, k1_zfmisc_1(k1_zfmisc_1(A_199))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.88/2.17  tff(c_2965, plain, (![A_1, D_196, C_198]: (u1_pre_topc(A_1)=D_196 | g1_pre_topc(C_198, D_196)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2961])).
% 5.88/2.17  tff(c_3436, plain, (![C_229, D_230]: (u1_pre_topc(g1_pre_topc(C_229, D_230))=D_230 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_229, D_230)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_229, D_230))))) | ~v1_pre_topc(g1_pre_topc(C_229, D_230)) | ~l1_pre_topc(g1_pre_topc(C_229, D_230)))), inference(reflexivity, [status(thm), theory('equality')], [c_2965])).
% 5.88/2.17  tff(c_3448, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3072, c_3436])).
% 5.88/2.17  tff(c_3463, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_3115, c_3448])).
% 5.88/2.17  tff(c_3479, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_3463])).
% 5.88/2.17  tff(c_3485, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_3479])).
% 5.88/2.17  tff(c_3491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_3485])).
% 5.88/2.17  tff(c_3492, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(splitRight, [status(thm)], [c_3463])).
% 5.88/2.17  tff(c_2993, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_2972])).
% 5.88/2.17  tff(c_3529, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3492, c_2993])).
% 5.88/2.17  tff(c_3534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3130, c_3529])).
% 5.88/2.17  tff(c_3535, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2939])).
% 5.88/2.17  tff(c_3538, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(negUnitSimplification, [status(thm)], [c_2917, c_36])).
% 5.88/2.17  tff(c_3565, plain, (![B_242, A_243]: (r2_hidden(B_242, u1_pre_topc(A_243)) | ~v3_pre_topc(B_242, A_243) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.88/2.17  tff(c_3568, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v3_pre_topc('#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_3538, c_3565])).
% 5.88/2.17  tff(c_3571, plain, (r2_hidden('#skF_2', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2916, c_3568])).
% 5.88/2.17  tff(c_3579, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_3571])).
% 5.88/2.17  tff(c_3585, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_3579])).
% 5.88/2.17  tff(c_3591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_3585])).
% 5.88/2.17  tff(c_3593, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_3571])).
% 5.88/2.17  tff(c_3549, plain, (![D_234, B_235, C_236, A_237]: (D_234=B_235 | g1_pre_topc(C_236, D_234)!=g1_pre_topc(A_237, B_235) | ~m1_subset_1(B_235, k1_zfmisc_1(k1_zfmisc_1(A_237))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.88/2.17  tff(c_3551, plain, (![A_1, B_235, A_237]: (u1_pre_topc(A_1)=B_235 | g1_pre_topc(A_237, B_235)!=A_1 | ~m1_subset_1(B_235, k1_zfmisc_1(k1_zfmisc_1(A_237))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3549])).
% 5.88/2.17  tff(c_3643, plain, (![A_258, B_259]: (u1_pre_topc(g1_pre_topc(A_258, B_259))=B_259 | ~m1_subset_1(B_259, k1_zfmisc_1(k1_zfmisc_1(A_258))) | ~v1_pre_topc(g1_pre_topc(A_258, B_259)) | ~l1_pre_topc(g1_pre_topc(A_258, B_259)))), inference(reflexivity, [status(thm), theory('equality')], [c_3551])).
% 5.88/2.17  tff(c_3654, plain, (![A_262]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_262), u1_pre_topc(A_262)))=u1_pre_topc(A_262) | ~v1_pre_topc(g1_pre_topc(u1_struct_0(A_262), u1_pre_topc(A_262))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_262), u1_pre_topc(A_262))) | ~l1_pre_topc(A_262))), inference(resolution, [status(thm)], [c_12, c_3643])).
% 5.88/2.17  tff(c_3662, plain, (![A_263]: (u1_pre_topc(g1_pre_topc(u1_struct_0(A_263), u1_pre_topc(A_263)))=u1_pre_topc(A_263) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_263), u1_pre_topc(A_263))) | ~l1_pre_topc(A_263))), inference(resolution, [status(thm)], [c_50, c_3654])).
% 5.88/2.17  tff(c_3665, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3593, c_3662])).
% 5.88/2.17  tff(c_3674, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3665])).
% 5.88/2.17  tff(c_3683, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3674, c_2])).
% 5.88/2.17  tff(c_3701, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_pre_topc('#skF_1'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3593, c_3683])).
% 5.88/2.17  tff(c_3878, plain, (~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_3701])).
% 5.88/2.17  tff(c_3884, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_3878])).
% 5.88/2.17  tff(c_3890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_3884])).
% 5.88/2.17  tff(c_3892, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_3701])).
% 5.88/2.17  tff(c_3692, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3674, c_12])).
% 5.88/2.17  tff(c_3707, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))))), inference(demodulation, [status(thm), theory('equality')], [c_3593, c_3692])).
% 5.88/2.17  tff(c_3558, plain, (![C_238, A_239, D_240, B_241]: (C_238=A_239 | g1_pre_topc(C_238, D_240)!=g1_pre_topc(A_239, B_241) | ~m1_subset_1(B_241, k1_zfmisc_1(k1_zfmisc_1(A_239))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.88/2.17  tff(c_3562, plain, (![A_1, C_238, D_240]: (u1_struct_0(A_1)=C_238 | g1_pre_topc(C_238, D_240)!=A_1 | ~m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3558])).
% 5.88/2.17  tff(c_3969, plain, (![C_271, D_272]: (u1_struct_0(g1_pre_topc(C_271, D_272))=C_271 | ~m1_subset_1(u1_pre_topc(g1_pre_topc(C_271, D_272)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(C_271, D_272))))) | ~v1_pre_topc(g1_pre_topc(C_271, D_272)) | ~l1_pre_topc(g1_pre_topc(C_271, D_272)))), inference(reflexivity, [status(thm), theory('equality')], [c_3562])).
% 5.88/2.17  tff(c_3981, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3674, c_3969])).
% 5.88/2.17  tff(c_3996, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3593, c_3892, c_3707, c_3981])).
% 5.88/2.17  tff(c_4000, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3996, c_3538])).
% 5.88/2.17  tff(c_4002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3535, c_4000])).
% 5.88/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.17  
% 5.88/2.17  Inference rules
% 5.88/2.17  ----------------------
% 5.88/2.17  #Ref     : 31
% 5.88/2.18  #Sup     : 891
% 5.88/2.18  #Fact    : 0
% 5.88/2.18  #Define  : 0
% 5.88/2.18  #Split   : 24
% 5.88/2.18  #Chain   : 0
% 5.88/2.18  #Close   : 0
% 5.88/2.18  
% 5.88/2.18  Ordering : KBO
% 5.88/2.18  
% 5.88/2.18  Simplification rules
% 5.88/2.18  ----------------------
% 5.88/2.18  #Subsume      : 216
% 5.88/2.18  #Demod        : 682
% 5.88/2.18  #Tautology    : 263
% 5.88/2.18  #SimpNegUnit  : 24
% 5.88/2.18  #BackRed      : 50
% 5.88/2.18  
% 5.88/2.18  #Partial instantiations: 0
% 5.88/2.18  #Strategies tried      : 1
% 5.88/2.18  
% 5.88/2.18  Timing (in seconds)
% 5.88/2.18  ----------------------
% 5.88/2.18  Preprocessing        : 0.31
% 5.88/2.18  Parsing              : 0.18
% 5.88/2.18  CNF conversion       : 0.02
% 5.88/2.18  Main loop            : 1.05
% 5.88/2.18  Inferencing          : 0.37
% 5.88/2.18  Reduction            : 0.33
% 5.88/2.18  Demodulation         : 0.23
% 5.88/2.18  BG Simplification    : 0.05
% 5.88/2.18  Subsumption          : 0.22
% 5.88/2.18  Abstraction          : 0.06
% 5.88/2.18  MUC search           : 0.00
% 5.88/2.18  Cooper               : 0.00
% 5.88/2.18  Total                : 1.44
% 5.88/2.18  Index Insertion      : 0.00
% 5.88/2.18  Index Deletion       : 0.00
% 5.88/2.18  Index Matching       : 0.00
% 5.88/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
