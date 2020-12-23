%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:01 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 277 expanded)
%              Number of leaves         :   34 ( 111 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 693 expanded)
%              Number of equality atoms :   30 ( 137 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v3_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v3_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).

tff(c_46,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    ~ v3_pre_topc('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58,plain,(
    ~ v3_pre_topc('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_90,plain,(
    ! [B_61,A_62] :
      ( l1_pre_topc(B_61)
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_93,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_90])).

tff(c_96,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_93])).

tff(c_32,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_75,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_79,plain,(
    ! [A_19] :
      ( u1_struct_0(A_19) = k2_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_109,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_79])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_57,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_110,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_57])).

tff(c_80,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_84,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_80])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_85,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_54])).

tff(c_50,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_172,plain,(
    ! [A_88,B_89,C_90] :
      ( r2_hidden('#skF_1'(A_88,B_89,C_90),A_88)
      | r2_hidden('#skF_2'(A_88,B_89,C_90),C_90)
      | k3_xboole_0(A_88,B_89) = C_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [C_12,A_9,B_10] :
      ( r2_hidden(C_12,A_9)
      | ~ r2_hidden(C_12,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1009,plain,(
    ! [A_217,B_218,C_219,A_220] :
      ( r2_hidden('#skF_1'(A_217,B_218,C_219),A_220)
      | ~ m1_subset_1(A_217,k1_zfmisc_1(A_220))
      | r2_hidden('#skF_2'(A_217,B_218,C_219),C_219)
      | k3_xboole_0(A_217,B_218) = C_219 ) ),
    inference(resolution,[status(thm)],[c_172,c_24])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1053,plain,(
    ! [A_221,A_222,B_223] :
      ( ~ m1_subset_1(A_221,k1_zfmisc_1(A_222))
      | r2_hidden('#skF_2'(A_221,B_223,A_222),A_222)
      | k3_xboole_0(A_221,B_223) = A_222 ) ),
    inference(resolution,[status(thm)],[c_1009,c_14])).

tff(c_1074,plain,(
    ! [A_221,B_223,A_222,A_9] :
      ( r2_hidden('#skF_2'(A_221,B_223,A_222),A_9)
      | ~ m1_subset_1(A_222,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(A_221,k1_zfmisc_1(A_222))
      | k3_xboole_0(A_221,B_223) = A_222 ) ),
    inference(resolution,[status(thm)],[c_1053,c_24])).

tff(c_1140,plain,(
    ! [A_232,B_233,C_234,A_235] :
      ( r2_hidden('#skF_2'(A_232,B_233,C_234),A_235)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(A_235))
      | r2_hidden('#skF_1'(A_232,B_233,C_234),A_232)
      | k3_xboole_0(A_232,B_233) = C_234 ) ),
    inference(resolution,[status(thm)],[c_172,c_24])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1422,plain,(
    ! [A_255,A_256,C_257] :
      ( ~ r2_hidden('#skF_2'(A_255,A_256,C_257),A_255)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(A_256))
      | r2_hidden('#skF_1'(A_255,A_256,C_257),A_255)
      | k3_xboole_0(A_255,A_256) = C_257 ) ),
    inference(resolution,[status(thm)],[c_1140,c_12])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1700,plain,(
    ! [A_277,A_278] :
      ( ~ r2_hidden('#skF_2'(A_277,A_278,A_277),A_278)
      | ~ r2_hidden('#skF_2'(A_277,A_278,A_277),A_277)
      | ~ m1_subset_1(A_277,k1_zfmisc_1(A_278))
      | k3_xboole_0(A_277,A_278) = A_277 ) ),
    inference(resolution,[status(thm)],[c_1422,c_8])).

tff(c_1717,plain,(
    ! [A_222,A_9] :
      ( ~ r2_hidden('#skF_2'(A_222,A_9,A_222),A_222)
      | ~ m1_subset_1(A_222,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(A_222,k1_zfmisc_1(A_222))
      | k3_xboole_0(A_222,A_9) = A_222 ) ),
    inference(resolution,[status(thm)],[c_1074,c_1700])).

tff(c_1811,plain,(
    ! [A_279,A_280] :
      ( ~ r2_hidden('#skF_2'(A_279,A_280,A_279),A_279)
      | ~ m1_subset_1(A_279,k1_zfmisc_1(A_280))
      | k3_xboole_0(A_279,A_280) = A_279 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_1717])).

tff(c_1833,plain,(
    ! [A_9,B_223] :
      ( ~ m1_subset_1(A_9,k1_zfmisc_1(B_223))
      | ~ m1_subset_1(A_9,k1_zfmisc_1(A_9))
      | k3_xboole_0(A_9,B_223) = A_9 ) ),
    inference(resolution,[status(thm)],[c_1074,c_1811])).

tff(c_1935,plain,(
    ! [A_281,B_282] :
      ( ~ m1_subset_1(A_281,k1_zfmisc_1(B_282))
      | k3_xboole_0(A_281,B_282) = A_281 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_1833])).

tff(c_1957,plain,(
    k3_xboole_0('#skF_5',k2_struct_0('#skF_6')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_110,c_1935])).

tff(c_118,plain,(
    ! [A_74,B_75,C_76] :
      ( k9_subset_1(A_74,B_75,C_76) = k3_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,(
    ! [A_8,B_75] : k9_subset_1(A_8,B_75,A_8) = k3_xboole_0(B_75,A_8) ),
    inference(resolution,[status(thm)],[c_59,c_118])).

tff(c_882,plain,(
    ! [B_202,D_203,A_204] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_202),D_203,k2_struct_0(B_202)),B_202)
      | ~ v3_pre_topc(D_203,A_204)
      | ~ m1_subset_1(D_203,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_202),D_203,k2_struct_0(B_202)),k1_zfmisc_1(u1_struct_0(B_202)))
      | ~ m1_pre_topc(B_202,A_204)
      | ~ l1_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_888,plain,(
    ! [B_202,D_203] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_202),D_203,k2_struct_0(B_202)),B_202)
      | ~ v3_pre_topc(D_203,'#skF_4')
      | ~ m1_subset_1(D_203,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_202),D_203,k2_struct_0(B_202)),k1_zfmisc_1(u1_struct_0(B_202)))
      | ~ m1_pre_topc(B_202,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_882])).

tff(c_3039,plain,(
    ! [B_353,D_354] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_353),D_354,k2_struct_0(B_353)),B_353)
      | ~ v3_pre_topc(D_354,'#skF_4')
      | ~ m1_subset_1(D_354,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_353),D_354,k2_struct_0(B_353)),k1_zfmisc_1(u1_struct_0(B_353)))
      | ~ m1_pre_topc(B_353,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_888])).

tff(c_3048,plain,(
    ! [D_354] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_6'),D_354,k2_struct_0('#skF_6')),'#skF_6')
      | ~ v3_pre_topc(D_354,'#skF_4')
      | ~ m1_subset_1(D_354,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_6'),D_354,k2_struct_0('#skF_6')),k1_zfmisc_1(k2_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_6','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_3039])).

tff(c_14127,plain,(
    ! [D_1031] :
      ( v3_pre_topc(k3_xboole_0(D_1031,k2_struct_0('#skF_6')),'#skF_6')
      | ~ v3_pre_topc(D_1031,'#skF_4')
      | ~ m1_subset_1(D_1031,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k3_xboole_0(D_1031,k2_struct_0('#skF_6')),k1_zfmisc_1(k2_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_127,c_109,c_127,c_109,c_3048])).

tff(c_14130,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_5',k2_struct_0('#skF_6')),'#skF_6')
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1957,c_14127])).

tff(c_14136,plain,(
    v3_pre_topc('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_85,c_50,c_1957,c_14130])).

tff(c_14138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_14136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:21:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.68/4.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.68/4.45  
% 11.68/4.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.68/4.46  %$ v3_pre_topc > r2_hidden > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 11.68/4.46  
% 11.68/4.46  %Foreground sorts:
% 11.68/4.46  
% 11.68/4.46  
% 11.68/4.46  %Background operators:
% 11.68/4.46  
% 11.68/4.46  
% 11.68/4.46  %Foreground operators:
% 11.68/4.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.68/4.46  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.68/4.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.68/4.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.68/4.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.68/4.46  tff('#skF_7', type, '#skF_7': $i).
% 11.68/4.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.68/4.46  tff('#skF_5', type, '#skF_5': $i).
% 11.68/4.46  tff('#skF_6', type, '#skF_6': $i).
% 11.68/4.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.68/4.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.68/4.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.68/4.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.68/4.46  tff('#skF_4', type, '#skF_4': $i).
% 11.68/4.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.68/4.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.68/4.46  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.68/4.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.68/4.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.68/4.46  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.68/4.46  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 11.68/4.46  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.68/4.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.68/4.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.68/4.46  
% 11.68/4.47  tff(f_101, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 11.68/4.47  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 11.68/4.47  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.68/4.47  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 11.68/4.47  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 11.68/4.47  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 11.68/4.47  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.68/4.47  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 11.68/4.47  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.68/4.47  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tops_2)).
% 11.68/4.47  tff(c_46, plain, ('#skF_7'='#skF_5'), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.68/4.47  tff(c_44, plain, (~v3_pre_topc('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.68/4.47  tff(c_58, plain, (~v3_pre_topc('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 11.68/4.47  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.68/4.47  tff(c_52, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.68/4.47  tff(c_90, plain, (![B_61, A_62]: (l1_pre_topc(B_61) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.68/4.47  tff(c_93, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_90])).
% 11.68/4.47  tff(c_96, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_93])).
% 11.68/4.47  tff(c_32, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.68/4.47  tff(c_75, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.68/4.47  tff(c_79, plain, (![A_19]: (u1_struct_0(A_19)=k2_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(resolution, [status(thm)], [c_32, c_75])).
% 11.68/4.47  tff(c_109, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_96, c_79])).
% 11.68/4.47  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.68/4.47  tff(c_57, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 11.68/4.47  tff(c_110, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_57])).
% 11.68/4.47  tff(c_80, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_32, c_75])).
% 11.68/4.47  tff(c_84, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_80])).
% 11.68/4.47  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.68/4.47  tff(c_85, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_54])).
% 11.68/4.47  tff(c_50, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.68/4.47  tff(c_20, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.68/4.47  tff(c_22, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.68/4.47  tff(c_59, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 11.68/4.47  tff(c_172, plain, (![A_88, B_89, C_90]: (r2_hidden('#skF_1'(A_88, B_89, C_90), A_88) | r2_hidden('#skF_2'(A_88, B_89, C_90), C_90) | k3_xboole_0(A_88, B_89)=C_90)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.68/4.47  tff(c_24, plain, (![C_12, A_9, B_10]: (r2_hidden(C_12, A_9) | ~r2_hidden(C_12, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.68/4.47  tff(c_1009, plain, (![A_217, B_218, C_219, A_220]: (r2_hidden('#skF_1'(A_217, B_218, C_219), A_220) | ~m1_subset_1(A_217, k1_zfmisc_1(A_220)) | r2_hidden('#skF_2'(A_217, B_218, C_219), C_219) | k3_xboole_0(A_217, B_218)=C_219)), inference(resolution, [status(thm)], [c_172, c_24])).
% 11.68/4.47  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.68/4.47  tff(c_1053, plain, (![A_221, A_222, B_223]: (~m1_subset_1(A_221, k1_zfmisc_1(A_222)) | r2_hidden('#skF_2'(A_221, B_223, A_222), A_222) | k3_xboole_0(A_221, B_223)=A_222)), inference(resolution, [status(thm)], [c_1009, c_14])).
% 11.68/4.47  tff(c_1074, plain, (![A_221, B_223, A_222, A_9]: (r2_hidden('#skF_2'(A_221, B_223, A_222), A_9) | ~m1_subset_1(A_222, k1_zfmisc_1(A_9)) | ~m1_subset_1(A_221, k1_zfmisc_1(A_222)) | k3_xboole_0(A_221, B_223)=A_222)), inference(resolution, [status(thm)], [c_1053, c_24])).
% 11.68/4.47  tff(c_1140, plain, (![A_232, B_233, C_234, A_235]: (r2_hidden('#skF_2'(A_232, B_233, C_234), A_235) | ~m1_subset_1(C_234, k1_zfmisc_1(A_235)) | r2_hidden('#skF_1'(A_232, B_233, C_234), A_232) | k3_xboole_0(A_232, B_233)=C_234)), inference(resolution, [status(thm)], [c_172, c_24])).
% 11.68/4.47  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.68/4.47  tff(c_1422, plain, (![A_255, A_256, C_257]: (~r2_hidden('#skF_2'(A_255, A_256, C_257), A_255) | ~m1_subset_1(C_257, k1_zfmisc_1(A_256)) | r2_hidden('#skF_1'(A_255, A_256, C_257), A_255) | k3_xboole_0(A_255, A_256)=C_257)), inference(resolution, [status(thm)], [c_1140, c_12])).
% 11.68/4.47  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.68/4.47  tff(c_1700, plain, (![A_277, A_278]: (~r2_hidden('#skF_2'(A_277, A_278, A_277), A_278) | ~r2_hidden('#skF_2'(A_277, A_278, A_277), A_277) | ~m1_subset_1(A_277, k1_zfmisc_1(A_278)) | k3_xboole_0(A_277, A_278)=A_277)), inference(resolution, [status(thm)], [c_1422, c_8])).
% 11.68/4.47  tff(c_1717, plain, (![A_222, A_9]: (~r2_hidden('#skF_2'(A_222, A_9, A_222), A_222) | ~m1_subset_1(A_222, k1_zfmisc_1(A_9)) | ~m1_subset_1(A_222, k1_zfmisc_1(A_222)) | k3_xboole_0(A_222, A_9)=A_222)), inference(resolution, [status(thm)], [c_1074, c_1700])).
% 11.68/4.47  tff(c_1811, plain, (![A_279, A_280]: (~r2_hidden('#skF_2'(A_279, A_280, A_279), A_279) | ~m1_subset_1(A_279, k1_zfmisc_1(A_280)) | k3_xboole_0(A_279, A_280)=A_279)), inference(demodulation, [status(thm), theory('equality')], [c_59, c_1717])).
% 11.68/4.47  tff(c_1833, plain, (![A_9, B_223]: (~m1_subset_1(A_9, k1_zfmisc_1(B_223)) | ~m1_subset_1(A_9, k1_zfmisc_1(A_9)) | k3_xboole_0(A_9, B_223)=A_9)), inference(resolution, [status(thm)], [c_1074, c_1811])).
% 11.68/4.47  tff(c_1935, plain, (![A_281, B_282]: (~m1_subset_1(A_281, k1_zfmisc_1(B_282)) | k3_xboole_0(A_281, B_282)=A_281)), inference(demodulation, [status(thm), theory('equality')], [c_59, c_1833])).
% 11.68/4.47  tff(c_1957, plain, (k3_xboole_0('#skF_5', k2_struct_0('#skF_6'))='#skF_5'), inference(resolution, [status(thm)], [c_110, c_1935])).
% 11.68/4.47  tff(c_118, plain, (![A_74, B_75, C_76]: (k9_subset_1(A_74, B_75, C_76)=k3_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.68/4.47  tff(c_127, plain, (![A_8, B_75]: (k9_subset_1(A_8, B_75, A_8)=k3_xboole_0(B_75, A_8))), inference(resolution, [status(thm)], [c_59, c_118])).
% 11.68/4.47  tff(c_882, plain, (![B_202, D_203, A_204]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_202), D_203, k2_struct_0(B_202)), B_202) | ~v3_pre_topc(D_203, A_204) | ~m1_subset_1(D_203, k1_zfmisc_1(u1_struct_0(A_204))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_202), D_203, k2_struct_0(B_202)), k1_zfmisc_1(u1_struct_0(B_202))) | ~m1_pre_topc(B_202, A_204) | ~l1_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.68/4.47  tff(c_888, plain, (![B_202, D_203]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_202), D_203, k2_struct_0(B_202)), B_202) | ~v3_pre_topc(D_203, '#skF_4') | ~m1_subset_1(D_203, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_202), D_203, k2_struct_0(B_202)), k1_zfmisc_1(u1_struct_0(B_202))) | ~m1_pre_topc(B_202, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_882])).
% 11.68/4.47  tff(c_3039, plain, (![B_353, D_354]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_353), D_354, k2_struct_0(B_353)), B_353) | ~v3_pre_topc(D_354, '#skF_4') | ~m1_subset_1(D_354, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_353), D_354, k2_struct_0(B_353)), k1_zfmisc_1(u1_struct_0(B_353))) | ~m1_pre_topc(B_353, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_888])).
% 11.68/4.47  tff(c_3048, plain, (![D_354]: (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_6'), D_354, k2_struct_0('#skF_6')), '#skF_6') | ~v3_pre_topc(D_354, '#skF_4') | ~m1_subset_1(D_354, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_6'), D_354, k2_struct_0('#skF_6')), k1_zfmisc_1(k2_struct_0('#skF_6'))) | ~m1_pre_topc('#skF_6', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_3039])).
% 11.68/4.47  tff(c_14127, plain, (![D_1031]: (v3_pre_topc(k3_xboole_0(D_1031, k2_struct_0('#skF_6')), '#skF_6') | ~v3_pre_topc(D_1031, '#skF_4') | ~m1_subset_1(D_1031, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k3_xboole_0(D_1031, k2_struct_0('#skF_6')), k1_zfmisc_1(k2_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_127, c_109, c_127, c_109, c_3048])).
% 11.68/4.47  tff(c_14130, plain, (v3_pre_topc(k3_xboole_0('#skF_5', k2_struct_0('#skF_6')), '#skF_6') | ~v3_pre_topc('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1957, c_14127])).
% 11.68/4.47  tff(c_14136, plain, (v3_pre_topc('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_85, c_50, c_1957, c_14130])).
% 11.68/4.47  tff(c_14138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_14136])).
% 11.68/4.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.68/4.47  
% 11.68/4.47  Inference rules
% 11.68/4.47  ----------------------
% 11.68/4.47  #Ref     : 0
% 11.68/4.47  #Sup     : 3361
% 11.68/4.47  #Fact    : 0
% 11.68/4.47  #Define  : 0
% 11.68/4.47  #Split   : 12
% 11.68/4.47  #Chain   : 0
% 11.68/4.47  #Close   : 0
% 11.68/4.47  
% 11.68/4.47  Ordering : KBO
% 11.68/4.47  
% 11.68/4.47  Simplification rules
% 11.68/4.47  ----------------------
% 11.68/4.47  #Subsume      : 1448
% 11.68/4.47  #Demod        : 2279
% 11.68/4.47  #Tautology    : 325
% 11.68/4.47  #SimpNegUnit  : 1
% 11.68/4.47  #BackRed      : 2
% 11.68/4.47  
% 11.68/4.47  #Partial instantiations: 0
% 11.68/4.47  #Strategies tried      : 1
% 11.68/4.47  
% 11.68/4.47  Timing (in seconds)
% 11.68/4.47  ----------------------
% 11.68/4.48  Preprocessing        : 0.32
% 11.68/4.48  Parsing              : 0.16
% 11.68/4.48  CNF conversion       : 0.02
% 11.68/4.48  Main loop            : 3.40
% 11.68/4.48  Inferencing          : 0.92
% 11.68/4.48  Reduction            : 0.84
% 11.68/4.48  Demodulation         : 0.57
% 11.68/4.48  BG Simplification    : 0.08
% 11.68/4.48  Subsumption          : 1.37
% 11.68/4.48  Abstraction          : 0.14
% 11.68/4.48  MUC search           : 0.00
% 11.68/4.48  Cooper               : 0.00
% 11.68/4.48  Total                : 3.75
% 11.68/4.48  Index Insertion      : 0.00
% 11.68/4.48  Index Deletion       : 0.00
% 11.68/4.48  Index Matching       : 0.00
% 11.68/4.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
