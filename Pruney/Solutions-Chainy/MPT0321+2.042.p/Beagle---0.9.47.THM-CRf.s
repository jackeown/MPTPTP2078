%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:19 EST 2020

% Result     : Theorem 5.00s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 348 expanded)
%              Number of leaves         :   29 ( 125 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 ( 756 expanded)
%              Number of equality atoms :   33 ( 225 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_74,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_58,plain,
    ( '#skF_11' != '#skF_9'
    | '#skF_10' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_67,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_698,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( r2_hidden(k4_tarski(A_128,B_129),k2_zfmisc_1(C_130,D_131))
      | ~ r2_hidden(B_129,D_131)
      | ~ r2_hidden(A_128,C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_64,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_221,plain,(
    ! [A_73,C_74,B_75,D_76] :
      ( r2_hidden(A_73,C_74)
      | ~ r2_hidden(k4_tarski(A_73,B_75),k2_zfmisc_1(C_74,D_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_224,plain,(
    ! [A_73,B_75] :
      ( r2_hidden(A_73,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_73,B_75),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_221])).

tff(c_724,plain,(
    ! [A_128,B_129] :
      ( r2_hidden(A_128,'#skF_10')
      | ~ r2_hidden(B_129,'#skF_9')
      | ~ r2_hidden(A_128,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_698,c_224])).

tff(c_731,plain,(
    ! [B_132] : ~ r2_hidden(B_132,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_724])).

tff(c_778,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_731])).

tff(c_50,plain,(
    ! [A_24] : r1_tarski(k1_xboole_0,A_24) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( r2_xboole_0(A_16,B_17)
      | B_17 = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_98,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_7'(A_45,B_46),B_46)
      | ~ r2_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [B_47,A_48] :
      ( ~ v1_xboole_0(B_47)
      | ~ r2_xboole_0(A_48,B_47) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_118,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | B_49 = A_50
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_122,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(resolution,[status(thm)],[c_50,c_118])).

tff(c_787,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_778,c_122])).

tff(c_794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_787])).

tff(c_796,plain,(
    ! [A_133] :
      ( r2_hidden(A_133,'#skF_10')
      | ~ r2_hidden(A_133,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_724])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_931,plain,(
    ! [A_138] :
      ( r1_tarski(A_138,'#skF_10')
      | ~ r2_hidden('#skF_2'(A_138,'#skF_10'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_796,c_8])).

tff(c_936,plain,(
    r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_10,c_931])).

tff(c_48,plain,(
    ! [A_21,B_22] :
      ( r2_hidden('#skF_7'(A_21,B_22),B_22)
      | ~ r2_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_185,plain,(
    ! [B_65,D_66,A_67,C_68] :
      ( r2_hidden(B_65,D_66)
      | ~ r2_hidden(k4_tarski(A_67,B_65),k2_zfmisc_1(C_68,D_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_188,plain,(
    ! [B_65,A_67] :
      ( r2_hidden(B_65,'#skF_11')
      | ~ r2_hidden(k4_tarski(A_67,B_65),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_185])).

tff(c_725,plain,(
    ! [B_129,A_128] :
      ( r2_hidden(B_129,'#skF_11')
      | ~ r2_hidden(B_129,'#skF_9')
      | ~ r2_hidden(A_128,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_698,c_188])).

tff(c_1020,plain,(
    ! [A_145] : ~ r2_hidden(A_145,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_725])).

tff(c_1079,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_1020])).

tff(c_1088,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1079,c_122])).

tff(c_1095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1088])).

tff(c_1097,plain,(
    ! [B_146] :
      ( r2_hidden(B_146,'#skF_11')
      | ~ r2_hidden(B_146,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_725])).

tff(c_1126,plain,(
    ! [B_146] :
      ( ~ v1_xboole_0('#skF_11')
      | ~ r2_hidden(B_146,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1097,c_2])).

tff(c_1189,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_1126])).

tff(c_937,plain,(
    ! [A_139,B_140] :
      ( r2_hidden(k4_tarski(A_139,B_140),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_140,'#skF_11')
      | ~ r2_hidden(A_139,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_698])).

tff(c_56,plain,(
    ! [A_25,C_27,B_26,D_28] :
      ( r2_hidden(A_25,C_27)
      | ~ r2_hidden(k4_tarski(A_25,B_26),k2_zfmisc_1(C_27,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_960,plain,(
    ! [A_139,B_140] :
      ( r2_hidden(A_139,'#skF_8')
      | ~ r2_hidden(B_140,'#skF_11')
      | ~ r2_hidden(A_139,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_937,c_56])).

tff(c_1309,plain,(
    ! [B_152] : ~ r2_hidden(B_152,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_960])).

tff(c_1357,plain,(
    v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_1309])).

tff(c_1371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1189,c_1357])).

tff(c_1373,plain,(
    ! [A_153] :
      ( r2_hidden(A_153,'#skF_8')
      | ~ r2_hidden(A_153,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_960])).

tff(c_2376,plain,(
    ! [A_199] :
      ( r2_hidden('#skF_7'(A_199,'#skF_10'),'#skF_8')
      | ~ r2_xboole_0(A_199,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_48,c_1373])).

tff(c_46,plain,(
    ! [A_21,B_22] :
      ( ~ r2_hidden('#skF_7'(A_21,B_22),A_21)
      | ~ r2_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2392,plain,(
    ~ r2_xboole_0('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_2376,c_46])).

tff(c_2396,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_2392])).

tff(c_2399,plain,(
    '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_2396])).

tff(c_2401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_2399])).

tff(c_2403,plain,(
    v1_xboole_0('#skF_11') ),
    inference(splitRight,[status(thm)],[c_1126])).

tff(c_2416,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_2403,c_122])).

tff(c_2705,plain,(
    '#skF_11' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2416,c_60])).

tff(c_2712,plain,(
    ! [B_215] : ~ r2_hidden(B_215,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1126])).

tff(c_2766,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_2712])).

tff(c_140,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_166,plain,(
    ! [A_58,B_59] :
      ( ~ v1_xboole_0(A_58)
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_117,plain,(
    ! [B_17,A_16] :
      ( ~ v1_xboole_0(B_17)
      | B_17 = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_170,plain,(
    ! [B_59,A_58] :
      ( ~ v1_xboole_0(B_59)
      | B_59 = A_58
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_166,c_117])).

tff(c_2828,plain,(
    ! [A_223] :
      ( A_223 = '#skF_11'
      | ~ v1_xboole_0(A_223) ) ),
    inference(resolution,[status(thm)],[c_2403,c_170])).

tff(c_2831,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2766,c_2828])).

tff(c_2841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2705,c_2831])).

tff(c_2842,plain,(
    '#skF_11' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2843,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2848,plain,(
    k2_zfmisc_1('#skF_8','#skF_11') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_64])).

tff(c_3669,plain,(
    ! [A_330,B_331,C_332,D_333] :
      ( r2_hidden(k4_tarski(A_330,B_331),k2_zfmisc_1(C_332,D_333))
      | ~ r2_hidden(B_331,D_333)
      | ~ r2_hidden(A_330,C_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4061,plain,(
    ! [A_351,B_352] :
      ( r2_hidden(k4_tarski(A_351,B_352),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_352,'#skF_11')
      | ~ r2_hidden(A_351,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2848,c_3669])).

tff(c_54,plain,(
    ! [B_26,D_28,A_25,C_27] :
      ( r2_hidden(B_26,D_28)
      | ~ r2_hidden(k4_tarski(A_25,B_26),k2_zfmisc_1(C_27,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4077,plain,(
    ! [B_352,A_351] :
      ( r2_hidden(B_352,'#skF_9')
      | ~ r2_hidden(B_352,'#skF_11')
      | ~ r2_hidden(A_351,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4061,c_54])).

tff(c_4256,plain,(
    ! [A_361] : ~ r2_hidden(A_361,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4077])).

tff(c_4320,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_4256])).

tff(c_2913,plain,(
    ! [A_246,B_247] :
      ( r2_hidden('#skF_7'(A_246,B_247),B_247)
      | ~ r2_xboole_0(A_246,B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2933,plain,(
    ! [B_248,A_249] :
      ( ~ v1_xboole_0(B_248)
      | ~ r2_xboole_0(A_249,B_248) ) ),
    inference(resolution,[status(thm)],[c_2913,c_2])).

tff(c_2948,plain,(
    ! [B_253,A_254] :
      ( ~ v1_xboole_0(B_253)
      | B_253 = A_254
      | ~ r1_tarski(A_254,B_253) ) ),
    inference(resolution,[status(thm)],[c_30,c_2933])).

tff(c_2961,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(resolution,[status(thm)],[c_50,c_2948])).

tff(c_4333,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4320,c_2961])).

tff(c_4342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4333])).

tff(c_4354,plain,(
    ! [B_362] :
      ( r2_hidden(B_362,'#skF_9')
      | ~ r2_hidden(B_362,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_4077])).

tff(c_4560,plain,(
    ! [A_371] :
      ( r2_hidden('#skF_7'(A_371,'#skF_11'),'#skF_9')
      | ~ r2_xboole_0(A_371,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_48,c_4354])).

tff(c_4576,plain,(
    ~ r2_xboole_0('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_4560,c_46])).

tff(c_4580,plain,
    ( '#skF_11' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_30,c_4576])).

tff(c_4583,plain,(
    ~ r1_tarski('#skF_9','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_2842,c_4580])).

tff(c_3008,plain,(
    ! [B_266,D_267,A_268,C_269] :
      ( r2_hidden(B_266,D_267)
      | ~ r2_hidden(k4_tarski(A_268,B_266),k2_zfmisc_1(C_269,D_267)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3011,plain,(
    ! [B_266,A_268] :
      ( r2_hidden(B_266,'#skF_11')
      | ~ r2_hidden(k4_tarski(A_268,B_266),k2_zfmisc_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2848,c_3008])).

tff(c_3688,plain,(
    ! [B_331,A_330] :
      ( r2_hidden(B_331,'#skF_11')
      | ~ r2_hidden(B_331,'#skF_9')
      | ~ r2_hidden(A_330,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3669,c_3011])).

tff(c_4112,plain,(
    ! [A_355] : ~ r2_hidden(A_355,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3688])).

tff(c_4171,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_4112])).

tff(c_4184,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4171,c_2961])).

tff(c_4193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4184])).

tff(c_4195,plain,(
    ! [B_356] :
      ( r2_hidden(B_356,'#skF_11')
      | ~ r2_hidden(B_356,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_3688])).

tff(c_4636,plain,(
    ! [A_375] :
      ( r1_tarski(A_375,'#skF_11')
      | ~ r2_hidden('#skF_2'(A_375,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4195,c_8])).

tff(c_4640,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_10,c_4636])).

tff(c_4644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4583,c_4583,c_4640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.00/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.93  
% 5.00/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.93  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_5
% 5.00/1.93  
% 5.00/1.93  %Foreground sorts:
% 5.00/1.93  
% 5.00/1.93  
% 5.00/1.93  %Background operators:
% 5.00/1.93  
% 5.00/1.93  
% 5.00/1.93  %Foreground operators:
% 5.00/1.93  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.00/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.00/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.00/1.93  tff('#skF_11', type, '#skF_11': $i).
% 5.00/1.93  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.00/1.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.00/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.00/1.93  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.00/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.00/1.93  tff('#skF_10', type, '#skF_10': $i).
% 5.00/1.93  tff('#skF_9', type, '#skF_9': $i).
% 5.00/1.93  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.00/1.93  tff('#skF_8', type, '#skF_8': $i).
% 5.00/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.00/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.00/1.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.00/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.00/1.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.00/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.00/1.93  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.00/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.00/1.93  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.00/1.93  
% 5.00/1.95  tff(f_91, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 5.00/1.95  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.00/1.95  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.00/1.95  tff(f_80, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.00/1.95  tff(f_74, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.00/1.95  tff(f_54, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 5.00/1.95  tff(f_72, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 5.00/1.95  tff(c_58, plain, ('#skF_11'!='#skF_9' | '#skF_10'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.00/1.95  tff(c_67, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_58])).
% 5.00/1.95  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.00/1.95  tff(c_60, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.00/1.95  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.00/1.95  tff(c_698, plain, (![A_128, B_129, C_130, D_131]: (r2_hidden(k4_tarski(A_128, B_129), k2_zfmisc_1(C_130, D_131)) | ~r2_hidden(B_129, D_131) | ~r2_hidden(A_128, C_130))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.00/1.95  tff(c_64, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.00/1.95  tff(c_221, plain, (![A_73, C_74, B_75, D_76]: (r2_hidden(A_73, C_74) | ~r2_hidden(k4_tarski(A_73, B_75), k2_zfmisc_1(C_74, D_76)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.00/1.95  tff(c_224, plain, (![A_73, B_75]: (r2_hidden(A_73, '#skF_10') | ~r2_hidden(k4_tarski(A_73, B_75), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_221])).
% 5.00/1.95  tff(c_724, plain, (![A_128, B_129]: (r2_hidden(A_128, '#skF_10') | ~r2_hidden(B_129, '#skF_9') | ~r2_hidden(A_128, '#skF_8'))), inference(resolution, [status(thm)], [c_698, c_224])).
% 5.00/1.95  tff(c_731, plain, (![B_132]: (~r2_hidden(B_132, '#skF_9'))), inference(splitLeft, [status(thm)], [c_724])).
% 5.00/1.95  tff(c_778, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_731])).
% 5.00/1.95  tff(c_50, plain, (![A_24]: (r1_tarski(k1_xboole_0, A_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.00/1.95  tff(c_30, plain, (![A_16, B_17]: (r2_xboole_0(A_16, B_17) | B_17=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.00/1.95  tff(c_98, plain, (![A_45, B_46]: (r2_hidden('#skF_7'(A_45, B_46), B_46) | ~r2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.00/1.95  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.00/1.95  tff(c_113, plain, (![B_47, A_48]: (~v1_xboole_0(B_47) | ~r2_xboole_0(A_48, B_47))), inference(resolution, [status(thm)], [c_98, c_2])).
% 5.00/1.95  tff(c_118, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | B_49=A_50 | ~r1_tarski(A_50, B_49))), inference(resolution, [status(thm)], [c_30, c_113])).
% 5.00/1.95  tff(c_122, plain, (![A_24]: (~v1_xboole_0(A_24) | k1_xboole_0=A_24)), inference(resolution, [status(thm)], [c_50, c_118])).
% 5.00/1.95  tff(c_787, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_778, c_122])).
% 5.00/1.95  tff(c_794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_787])).
% 5.00/1.95  tff(c_796, plain, (![A_133]: (r2_hidden(A_133, '#skF_10') | ~r2_hidden(A_133, '#skF_8'))), inference(splitRight, [status(thm)], [c_724])).
% 5.00/1.95  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.00/1.95  tff(c_931, plain, (![A_138]: (r1_tarski(A_138, '#skF_10') | ~r2_hidden('#skF_2'(A_138, '#skF_10'), '#skF_8'))), inference(resolution, [status(thm)], [c_796, c_8])).
% 5.00/1.95  tff(c_936, plain, (r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_10, c_931])).
% 5.00/1.95  tff(c_48, plain, (![A_21, B_22]: (r2_hidden('#skF_7'(A_21, B_22), B_22) | ~r2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.00/1.95  tff(c_62, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.00/1.95  tff(c_185, plain, (![B_65, D_66, A_67, C_68]: (r2_hidden(B_65, D_66) | ~r2_hidden(k4_tarski(A_67, B_65), k2_zfmisc_1(C_68, D_66)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.00/1.95  tff(c_188, plain, (![B_65, A_67]: (r2_hidden(B_65, '#skF_11') | ~r2_hidden(k4_tarski(A_67, B_65), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_185])).
% 5.00/1.95  tff(c_725, plain, (![B_129, A_128]: (r2_hidden(B_129, '#skF_11') | ~r2_hidden(B_129, '#skF_9') | ~r2_hidden(A_128, '#skF_8'))), inference(resolution, [status(thm)], [c_698, c_188])).
% 5.00/1.95  tff(c_1020, plain, (![A_145]: (~r2_hidden(A_145, '#skF_8'))), inference(splitLeft, [status(thm)], [c_725])).
% 5.00/1.95  tff(c_1079, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_1020])).
% 5.00/1.95  tff(c_1088, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1079, c_122])).
% 5.00/1.95  tff(c_1095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1088])).
% 5.00/1.95  tff(c_1097, plain, (![B_146]: (r2_hidden(B_146, '#skF_11') | ~r2_hidden(B_146, '#skF_9'))), inference(splitRight, [status(thm)], [c_725])).
% 5.00/1.95  tff(c_1126, plain, (![B_146]: (~v1_xboole_0('#skF_11') | ~r2_hidden(B_146, '#skF_9'))), inference(resolution, [status(thm)], [c_1097, c_2])).
% 5.00/1.95  tff(c_1189, plain, (~v1_xboole_0('#skF_11')), inference(splitLeft, [status(thm)], [c_1126])).
% 5.00/1.95  tff(c_937, plain, (![A_139, B_140]: (r2_hidden(k4_tarski(A_139, B_140), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_140, '#skF_11') | ~r2_hidden(A_139, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_698])).
% 5.00/1.95  tff(c_56, plain, (![A_25, C_27, B_26, D_28]: (r2_hidden(A_25, C_27) | ~r2_hidden(k4_tarski(A_25, B_26), k2_zfmisc_1(C_27, D_28)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.00/1.95  tff(c_960, plain, (![A_139, B_140]: (r2_hidden(A_139, '#skF_8') | ~r2_hidden(B_140, '#skF_11') | ~r2_hidden(A_139, '#skF_10'))), inference(resolution, [status(thm)], [c_937, c_56])).
% 5.00/1.95  tff(c_1309, plain, (![B_152]: (~r2_hidden(B_152, '#skF_11'))), inference(splitLeft, [status(thm)], [c_960])).
% 5.00/1.95  tff(c_1357, plain, (v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_4, c_1309])).
% 5.00/1.95  tff(c_1371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1189, c_1357])).
% 5.00/1.95  tff(c_1373, plain, (![A_153]: (r2_hidden(A_153, '#skF_8') | ~r2_hidden(A_153, '#skF_10'))), inference(splitRight, [status(thm)], [c_960])).
% 5.00/1.95  tff(c_2376, plain, (![A_199]: (r2_hidden('#skF_7'(A_199, '#skF_10'), '#skF_8') | ~r2_xboole_0(A_199, '#skF_10'))), inference(resolution, [status(thm)], [c_48, c_1373])).
% 5.00/1.95  tff(c_46, plain, (![A_21, B_22]: (~r2_hidden('#skF_7'(A_21, B_22), A_21) | ~r2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.00/1.95  tff(c_2392, plain, (~r2_xboole_0('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_2376, c_46])).
% 5.00/1.95  tff(c_2396, plain, ('#skF_10'='#skF_8' | ~r1_tarski('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_30, c_2392])).
% 5.00/1.95  tff(c_2399, plain, ('#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_936, c_2396])).
% 5.00/1.95  tff(c_2401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_2399])).
% 5.00/1.95  tff(c_2403, plain, (v1_xboole_0('#skF_11')), inference(splitRight, [status(thm)], [c_1126])).
% 5.00/1.95  tff(c_2416, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_2403, c_122])).
% 5.00/1.95  tff(c_2705, plain, ('#skF_11'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2416, c_60])).
% 5.00/1.95  tff(c_2712, plain, (![B_215]: (~r2_hidden(B_215, '#skF_9'))), inference(splitRight, [status(thm)], [c_1126])).
% 5.00/1.95  tff(c_2766, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_2712])).
% 5.00/1.95  tff(c_140, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.00/1.95  tff(c_166, plain, (![A_58, B_59]: (~v1_xboole_0(A_58) | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_140, c_2])).
% 5.00/1.95  tff(c_117, plain, (![B_17, A_16]: (~v1_xboole_0(B_17) | B_17=A_16 | ~r1_tarski(A_16, B_17))), inference(resolution, [status(thm)], [c_30, c_113])).
% 5.00/1.95  tff(c_170, plain, (![B_59, A_58]: (~v1_xboole_0(B_59) | B_59=A_58 | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_166, c_117])).
% 5.00/1.95  tff(c_2828, plain, (![A_223]: (A_223='#skF_11' | ~v1_xboole_0(A_223))), inference(resolution, [status(thm)], [c_2403, c_170])).
% 5.00/1.95  tff(c_2831, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_2766, c_2828])).
% 5.00/1.95  tff(c_2841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2705, c_2831])).
% 5.00/1.95  tff(c_2842, plain, ('#skF_11'!='#skF_9'), inference(splitRight, [status(thm)], [c_58])).
% 5.00/1.95  tff(c_2843, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_58])).
% 5.00/1.95  tff(c_2848, plain, (k2_zfmisc_1('#skF_8', '#skF_11')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_64])).
% 5.00/1.95  tff(c_3669, plain, (![A_330, B_331, C_332, D_333]: (r2_hidden(k4_tarski(A_330, B_331), k2_zfmisc_1(C_332, D_333)) | ~r2_hidden(B_331, D_333) | ~r2_hidden(A_330, C_332))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.00/1.95  tff(c_4061, plain, (![A_351, B_352]: (r2_hidden(k4_tarski(A_351, B_352), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_352, '#skF_11') | ~r2_hidden(A_351, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2848, c_3669])).
% 5.00/1.95  tff(c_54, plain, (![B_26, D_28, A_25, C_27]: (r2_hidden(B_26, D_28) | ~r2_hidden(k4_tarski(A_25, B_26), k2_zfmisc_1(C_27, D_28)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.00/1.95  tff(c_4077, plain, (![B_352, A_351]: (r2_hidden(B_352, '#skF_9') | ~r2_hidden(B_352, '#skF_11') | ~r2_hidden(A_351, '#skF_8'))), inference(resolution, [status(thm)], [c_4061, c_54])).
% 5.00/1.95  tff(c_4256, plain, (![A_361]: (~r2_hidden(A_361, '#skF_8'))), inference(splitLeft, [status(thm)], [c_4077])).
% 5.00/1.95  tff(c_4320, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_4256])).
% 5.00/1.95  tff(c_2913, plain, (![A_246, B_247]: (r2_hidden('#skF_7'(A_246, B_247), B_247) | ~r2_xboole_0(A_246, B_247))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.00/1.95  tff(c_2933, plain, (![B_248, A_249]: (~v1_xboole_0(B_248) | ~r2_xboole_0(A_249, B_248))), inference(resolution, [status(thm)], [c_2913, c_2])).
% 5.00/1.95  tff(c_2948, plain, (![B_253, A_254]: (~v1_xboole_0(B_253) | B_253=A_254 | ~r1_tarski(A_254, B_253))), inference(resolution, [status(thm)], [c_30, c_2933])).
% 5.00/1.95  tff(c_2961, plain, (![A_24]: (~v1_xboole_0(A_24) | k1_xboole_0=A_24)), inference(resolution, [status(thm)], [c_50, c_2948])).
% 5.00/1.95  tff(c_4333, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_4320, c_2961])).
% 5.00/1.95  tff(c_4342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_4333])).
% 5.00/1.95  tff(c_4354, plain, (![B_362]: (r2_hidden(B_362, '#skF_9') | ~r2_hidden(B_362, '#skF_11'))), inference(splitRight, [status(thm)], [c_4077])).
% 5.00/1.95  tff(c_4560, plain, (![A_371]: (r2_hidden('#skF_7'(A_371, '#skF_11'), '#skF_9') | ~r2_xboole_0(A_371, '#skF_11'))), inference(resolution, [status(thm)], [c_48, c_4354])).
% 5.00/1.95  tff(c_4576, plain, (~r2_xboole_0('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_4560, c_46])).
% 5.00/1.95  tff(c_4580, plain, ('#skF_11'='#skF_9' | ~r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_30, c_4576])).
% 5.00/1.95  tff(c_4583, plain, (~r1_tarski('#skF_9', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_2842, c_4580])).
% 5.00/1.95  tff(c_3008, plain, (![B_266, D_267, A_268, C_269]: (r2_hidden(B_266, D_267) | ~r2_hidden(k4_tarski(A_268, B_266), k2_zfmisc_1(C_269, D_267)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.00/1.95  tff(c_3011, plain, (![B_266, A_268]: (r2_hidden(B_266, '#skF_11') | ~r2_hidden(k4_tarski(A_268, B_266), k2_zfmisc_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_2848, c_3008])).
% 5.00/1.95  tff(c_3688, plain, (![B_331, A_330]: (r2_hidden(B_331, '#skF_11') | ~r2_hidden(B_331, '#skF_9') | ~r2_hidden(A_330, '#skF_8'))), inference(resolution, [status(thm)], [c_3669, c_3011])).
% 5.00/1.95  tff(c_4112, plain, (![A_355]: (~r2_hidden(A_355, '#skF_8'))), inference(splitLeft, [status(thm)], [c_3688])).
% 5.00/1.95  tff(c_4171, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_4112])).
% 5.00/1.95  tff(c_4184, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_4171, c_2961])).
% 5.00/1.95  tff(c_4193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_4184])).
% 5.00/1.95  tff(c_4195, plain, (![B_356]: (r2_hidden(B_356, '#skF_11') | ~r2_hidden(B_356, '#skF_9'))), inference(splitRight, [status(thm)], [c_3688])).
% 5.00/1.95  tff(c_4636, plain, (![A_375]: (r1_tarski(A_375, '#skF_11') | ~r2_hidden('#skF_2'(A_375, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_4195, c_8])).
% 5.00/1.95  tff(c_4640, plain, (r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_10, c_4636])).
% 5.00/1.95  tff(c_4644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4583, c_4583, c_4640])).
% 5.00/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.95  
% 5.00/1.95  Inference rules
% 5.00/1.95  ----------------------
% 5.00/1.95  #Ref     : 0
% 5.00/1.95  #Sup     : 978
% 5.00/1.95  #Fact    : 0
% 5.00/1.95  #Define  : 0
% 5.00/1.95  #Split   : 19
% 5.00/1.95  #Chain   : 0
% 5.00/1.95  #Close   : 0
% 5.00/1.95  
% 5.00/1.95  Ordering : KBO
% 5.00/1.95  
% 5.00/1.95  Simplification rules
% 5.00/1.95  ----------------------
% 5.00/1.95  #Subsume      : 230
% 5.00/1.95  #Demod        : 262
% 5.00/1.95  #Tautology    : 232
% 5.00/1.95  #SimpNegUnit  : 45
% 5.00/1.95  #BackRed      : 84
% 5.00/1.95  
% 5.00/1.95  #Partial instantiations: 0
% 5.00/1.95  #Strategies tried      : 1
% 5.00/1.95  
% 5.00/1.95  Timing (in seconds)
% 5.00/1.95  ----------------------
% 5.00/1.96  Preprocessing        : 0.32
% 5.00/1.96  Parsing              : 0.17
% 5.00/1.96  CNF conversion       : 0.03
% 5.00/1.96  Main loop            : 0.86
% 5.00/1.96  Inferencing          : 0.32
% 5.00/1.96  Reduction            : 0.22
% 5.00/1.96  Demodulation         : 0.14
% 5.00/1.96  BG Simplification    : 0.04
% 5.00/1.96  Subsumption          : 0.19
% 5.00/1.96  Abstraction          : 0.04
% 5.00/1.96  MUC search           : 0.00
% 5.00/1.96  Cooper               : 0.00
% 5.00/1.96  Total                : 1.22
% 5.00/1.96  Index Insertion      : 0.00
% 5.00/1.96  Index Deletion       : 0.00
% 5.00/1.96  Index Matching       : 0.00
% 5.00/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
