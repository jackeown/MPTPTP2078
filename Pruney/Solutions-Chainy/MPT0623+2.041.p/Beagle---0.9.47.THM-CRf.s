%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:11 EST 2020

% Result     : Theorem 10.20s
% Output     : CNFRefutation 10.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 298 expanded)
%              Number of leaves         :   40 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          :  200 ( 752 expanded)
%              Number of equality atoms :  100 ( 382 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_97,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_66,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_110,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_62,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_66,plain,(
    ! [A_33] : v1_relat_1('#skF_7'(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    ! [A_33] : v1_funct_1('#skF_7'(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_62,plain,(
    ! [A_33] : k1_relat_1('#skF_7'(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_78,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_93,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_36,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_103,plain,(
    ! [B_60,A_61] :
      ( r1_xboole_0(B_60,A_61)
      | ~ r1_xboole_0(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_106,plain,(
    ! [A_22] : r1_xboole_0(k1_xboole_0,A_22) ),
    inference(resolution,[status(thm)],[c_36,c_103])).

tff(c_135,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = A_69
      | ~ r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_146,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_135])).

tff(c_1584,plain,(
    ! [A_193,B_194,C_195] :
      ( r2_hidden('#skF_2'(A_193,B_194,C_195),A_193)
      | r2_hidden('#skF_3'(A_193,B_194,C_195),C_195)
      | k4_xboole_0(A_193,B_194) = C_195 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_206,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k4_xboole_0(A_83,B_84)) = k3_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_246,plain,(
    ! [B_88] : k3_xboole_0(k1_xboole_0,B_88) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_146])).

tff(c_30,plain,(
    ! [A_14,B_15,C_18] :
      ( ~ r1_xboole_0(A_14,B_15)
      | ~ r2_hidden(C_18,k3_xboole_0(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_251,plain,(
    ! [B_88,C_18] :
      ( ~ r1_xboole_0(k1_xboole_0,B_88)
      | ~ r2_hidden(C_18,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_30])).

tff(c_256,plain,(
    ! [C_18] : ~ r2_hidden(C_18,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_251])).

tff(c_1605,plain,(
    ! [B_194,C_195] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_194,C_195),C_195)
      | k4_xboole_0(k1_xboole_0,B_194) = C_195 ) ),
    inference(resolution,[status(thm)],[c_1584,c_256])).

tff(c_1667,plain,(
    ! [B_196,C_197] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_196,C_197),C_197)
      | k1_xboole_0 = C_197 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_1605])).

tff(c_1724,plain,(
    ! [A_199,B_200] :
      ( ~ r1_xboole_0(A_199,B_200)
      | k3_xboole_0(A_199,B_200) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1667,c_30])).

tff(c_1765,plain,(
    ! [A_22] : k3_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1724])).

tff(c_147,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(resolution,[status(thm)],[c_36,c_135])).

tff(c_235,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k3_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_206])).

tff(c_1782,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_235])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1970,plain,(
    ! [A_208,B_209,C_210] :
      ( ~ r2_hidden('#skF_2'(A_208,B_209,C_210),B_209)
      | r2_hidden('#skF_3'(A_208,B_209,C_210),C_210)
      | k4_xboole_0(A_208,B_209) = C_210 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1973,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_1970])).

tff(c_1978,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k1_xboole_0 = C_8 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1782,c_1973])).

tff(c_70,plain,(
    ! [A_39,B_43] :
      ( k1_relat_1('#skF_8'(A_39,B_43)) = A_39
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_72,plain,(
    ! [A_39,B_43] :
      ( v1_funct_1('#skF_8'(A_39,B_43))
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_74,plain,(
    ! [A_39,B_43] :
      ( v1_relat_1('#skF_8'(A_39,B_43))
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_189,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(A_78,B_79),A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_566,plain,(
    ! [A_131,B_132] :
      ( '#skF_1'(k1_tarski(A_131),B_132) = A_131
      | r1_tarski(k1_tarski(A_131),B_132) ) ),
    inference(resolution,[status(thm)],[c_189,c_42])).

tff(c_266,plain,(
    ! [A_90,B_91] :
      ( k2_relat_1('#skF_8'(A_90,B_91)) = k1_tarski(B_91)
      | k1_xboole_0 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_76,plain,(
    ! [C_46] :
      ( ~ r1_tarski(k2_relat_1(C_46),'#skF_9')
      | k1_relat_1(C_46) != '#skF_10'
      | ~ v1_funct_1(C_46)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_272,plain,(
    ! [B_91,A_90] :
      ( ~ r1_tarski(k1_tarski(B_91),'#skF_9')
      | k1_relat_1('#skF_8'(A_90,B_91)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_90,B_91))
      | ~ v1_relat_1('#skF_8'(A_90,B_91))
      | k1_xboole_0 = A_90 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_76])).

tff(c_608,plain,(
    ! [A_141,A_142] :
      ( k1_relat_1('#skF_8'(A_141,A_142)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_141,A_142))
      | ~ v1_relat_1('#skF_8'(A_141,A_142))
      | k1_xboole_0 = A_141
      | '#skF_1'(k1_tarski(A_142),'#skF_9') = A_142 ) ),
    inference(resolution,[status(thm)],[c_566,c_272])).

tff(c_953,plain,(
    ! [A_159,B_160] :
      ( k1_relat_1('#skF_8'(A_159,B_160)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_159,B_160))
      | '#skF_1'(k1_tarski(B_160),'#skF_9') = B_160
      | k1_xboole_0 = A_159 ) ),
    inference(resolution,[status(thm)],[c_74,c_608])).

tff(c_3449,plain,(
    ! [A_284,B_285] :
      ( k1_relat_1('#skF_8'(A_284,B_285)) != '#skF_10'
      | '#skF_1'(k1_tarski(B_285),'#skF_9') = B_285
      | k1_xboole_0 = A_284 ) ),
    inference(resolution,[status(thm)],[c_72,c_953])).

tff(c_3452,plain,(
    ! [A_39,B_43] :
      ( A_39 != '#skF_10'
      | '#skF_1'(k1_tarski(B_43),'#skF_9') = B_43
      | k1_xboole_0 = A_39
      | k1_xboole_0 = A_39 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_3449])).

tff(c_4047,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_3452])).

tff(c_32,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_343,plain,(
    ! [A_97] :
      ( k2_relat_1(A_97) = k1_xboole_0
      | k1_relat_1(A_97) != k1_xboole_0
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_349,plain,(
    ! [A_33] :
      ( k2_relat_1('#skF_7'(A_33)) = k1_xboole_0
      | k1_relat_1('#skF_7'(A_33)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_343])).

tff(c_355,plain,(
    ! [A_99] :
      ( k2_relat_1('#skF_7'(A_99)) = k1_xboole_0
      | k1_xboole_0 != A_99 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_349])).

tff(c_364,plain,(
    ! [A_99] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_9')
      | k1_relat_1('#skF_7'(A_99)) != '#skF_10'
      | ~ v1_funct_1('#skF_7'(A_99))
      | ~ v1_relat_1('#skF_7'(A_99))
      | k1_xboole_0 != A_99 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_76])).

tff(c_371,plain,(
    ! [A_99] :
      ( A_99 != '#skF_10'
      | k1_xboole_0 != A_99 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_32,c_364])).

tff(c_376,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_371])).

tff(c_4101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4047,c_376])).

tff(c_4104,plain,(
    ! [B_299] : '#skF_1'(k1_tarski(B_299),'#skF_9') = B_299 ),
    inference(splitRight,[status(thm)],[c_3452])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4129,plain,(
    ! [B_300] :
      ( ~ r2_hidden(B_300,'#skF_9')
      | r1_tarski(k1_tarski(B_300),'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4104,c_4])).

tff(c_4344,plain,(
    ! [A_306,B_307] :
      ( k1_relat_1('#skF_8'(A_306,B_307)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_306,B_307))
      | ~ v1_relat_1('#skF_8'(A_306,B_307))
      | k1_xboole_0 = A_306
      | ~ r2_hidden(B_307,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_4129,c_272])).

tff(c_27036,plain,(
    ! [A_12339,B_12340] :
      ( k1_relat_1('#skF_8'(A_12339,B_12340)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_12339,B_12340))
      | ~ r2_hidden(B_12340,'#skF_9')
      | k1_xboole_0 = A_12339 ) ),
    inference(resolution,[status(thm)],[c_74,c_4344])).

tff(c_33146,plain,(
    ! [A_13781,B_13782] :
      ( k1_relat_1('#skF_8'(A_13781,B_13782)) != '#skF_10'
      | ~ r2_hidden(B_13782,'#skF_9')
      | k1_xboole_0 = A_13781 ) ),
    inference(resolution,[status(thm)],[c_72,c_27036])).

tff(c_33151,plain,(
    ! [A_39,B_43] :
      ( A_39 != '#skF_10'
      | ~ r2_hidden(B_43,'#skF_9')
      | k1_xboole_0 = A_39
      | k1_xboole_0 = A_39 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_33146])).

tff(c_33153,plain,(
    ! [B_13812] : ~ r2_hidden(B_13812,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_33151])).

tff(c_33209,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1978,c_33153])).

tff(c_33257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_33209])).

tff(c_33259,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_33151])).

tff(c_33382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33259,c_376])).

tff(c_33384,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_33383,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_33391,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33384,c_33383])).

tff(c_33385,plain,(
    ! [A_19] : r1_tarski('#skF_10',A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33383,c_32])).

tff(c_33402,plain,(
    ! [A_19] : r1_tarski('#skF_9',A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33391,c_33385])).

tff(c_58,plain,(
    ! [A_32] :
      ( k2_relat_1(A_32) = k1_xboole_0
      | k1_relat_1(A_32) != k1_xboole_0
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_33515,plain,(
    ! [A_13871] :
      ( k2_relat_1(A_13871) = '#skF_9'
      | k1_relat_1(A_13871) != '#skF_9'
      | ~ v1_relat_1(A_13871) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33384,c_33384,c_58])).

tff(c_33521,plain,(
    ! [A_33] :
      ( k2_relat_1('#skF_7'(A_33)) = '#skF_9'
      | k1_relat_1('#skF_7'(A_33)) != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_66,c_33515])).

tff(c_33526,plain,(
    ! [A_13872] :
      ( k2_relat_1('#skF_7'(A_13872)) = '#skF_9'
      | A_13872 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_33521])).

tff(c_33410,plain,(
    ! [C_46] :
      ( ~ r1_tarski(k2_relat_1(C_46),'#skF_9')
      | k1_relat_1(C_46) != '#skF_9'
      | ~ v1_funct_1(C_46)
      | ~ v1_relat_1(C_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33391,c_76])).

tff(c_33532,plain,(
    ! [A_13872] :
      ( ~ r1_tarski('#skF_9','#skF_9')
      | k1_relat_1('#skF_7'(A_13872)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_13872))
      | ~ v1_relat_1('#skF_7'(A_13872))
      | A_13872 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33526,c_33410])).

tff(c_33538,plain,(
    ! [A_13872] : A_13872 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_33402,c_33532])).

tff(c_33386,plain,(
    ! [A_22] : r1_xboole_0(A_22,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33383,c_36])).

tff(c_33400,plain,(
    ! [A_22] : r1_xboole_0(A_22,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33391,c_33386])).

tff(c_33416,plain,(
    ! [B_13851,A_13852] :
      ( r1_xboole_0(B_13851,A_13852)
      | ~ r1_xboole_0(A_13852,B_13851) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_33419,plain,(
    ! [A_22] : r1_xboole_0('#skF_9',A_22) ),
    inference(resolution,[status(thm)],[c_33400,c_33416])).

tff(c_33425,plain,(
    ! [A_13854,B_13855] :
      ( k4_xboole_0(A_13854,B_13855) = A_13854
      | ~ r1_xboole_0(A_13854,B_13855) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_33432,plain,(
    ! [A_22] : k4_xboole_0('#skF_9',A_22) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_33419,c_33425])).

tff(c_33581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33538,c_33432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:28:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.20/3.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.20/3.84  
% 10.20/3.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.20/3.84  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 10.20/3.84  
% 10.20/3.84  %Foreground sorts:
% 10.20/3.84  
% 10.20/3.84  
% 10.20/3.84  %Background operators:
% 10.20/3.84  
% 10.20/3.84  
% 10.20/3.84  %Foreground operators:
% 10.20/3.84  tff('#skF_7', type, '#skF_7': $i > $i).
% 10.20/3.84  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.20/3.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.20/3.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.20/3.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.20/3.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.20/3.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.20/3.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.20/3.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.20/3.84  tff('#skF_10', type, '#skF_10': $i).
% 10.20/3.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.20/3.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.20/3.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.20/3.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.20/3.84  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 10.20/3.84  tff('#skF_9', type, '#skF_9': $i).
% 10.20/3.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.20/3.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.20/3.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.20/3.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.20/3.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.20/3.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.20/3.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.20/3.84  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.20/3.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.20/3.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.20/3.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.20/3.84  
% 10.20/3.86  tff(f_97, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 10.20/3.86  tff(f_128, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 10.20/3.86  tff(f_66, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.20/3.86  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.20/3.86  tff(f_70, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.20/3.86  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.20/3.86  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.20/3.86  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.20/3.86  tff(f_110, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 10.20/3.86  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.20/3.86  tff(f_77, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 10.20/3.86  tff(f_62, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.20/3.86  tff(f_85, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 10.20/3.86  tff(c_66, plain, (![A_33]: (v1_relat_1('#skF_7'(A_33)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.20/3.86  tff(c_64, plain, (![A_33]: (v1_funct_1('#skF_7'(A_33)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.20/3.86  tff(c_62, plain, (![A_33]: (k1_relat_1('#skF_7'(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.20/3.86  tff(c_78, plain, (k1_xboole_0='#skF_10' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.20/3.86  tff(c_93, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_78])).
% 10.20/3.86  tff(c_36, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.20/3.86  tff(c_103, plain, (![B_60, A_61]: (r1_xboole_0(B_60, A_61) | ~r1_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.20/3.86  tff(c_106, plain, (![A_22]: (r1_xboole_0(k1_xboole_0, A_22))), inference(resolution, [status(thm)], [c_36, c_103])).
% 10.20/3.86  tff(c_135, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=A_69 | ~r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.20/3.86  tff(c_146, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_106, c_135])).
% 10.20/3.86  tff(c_1584, plain, (![A_193, B_194, C_195]: (r2_hidden('#skF_2'(A_193, B_194, C_195), A_193) | r2_hidden('#skF_3'(A_193, B_194, C_195), C_195) | k4_xboole_0(A_193, B_194)=C_195)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.20/3.86  tff(c_206, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k4_xboole_0(A_83, B_84))=k3_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.20/3.86  tff(c_246, plain, (![B_88]: (k3_xboole_0(k1_xboole_0, B_88)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_206, c_146])).
% 10.20/3.86  tff(c_30, plain, (![A_14, B_15, C_18]: (~r1_xboole_0(A_14, B_15) | ~r2_hidden(C_18, k3_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.20/3.86  tff(c_251, plain, (![B_88, C_18]: (~r1_xboole_0(k1_xboole_0, B_88) | ~r2_hidden(C_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_246, c_30])).
% 10.20/3.86  tff(c_256, plain, (![C_18]: (~r2_hidden(C_18, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_251])).
% 10.20/3.86  tff(c_1605, plain, (![B_194, C_195]: (r2_hidden('#skF_3'(k1_xboole_0, B_194, C_195), C_195) | k4_xboole_0(k1_xboole_0, B_194)=C_195)), inference(resolution, [status(thm)], [c_1584, c_256])).
% 10.20/3.86  tff(c_1667, plain, (![B_196, C_197]: (r2_hidden('#skF_3'(k1_xboole_0, B_196, C_197), C_197) | k1_xboole_0=C_197)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_1605])).
% 10.20/3.86  tff(c_1724, plain, (![A_199, B_200]: (~r1_xboole_0(A_199, B_200) | k3_xboole_0(A_199, B_200)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1667, c_30])).
% 10.20/3.86  tff(c_1765, plain, (![A_22]: (k3_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_1724])).
% 10.20/3.86  tff(c_147, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(resolution, [status(thm)], [c_36, c_135])).
% 10.20/3.86  tff(c_235, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k3_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_147, c_206])).
% 10.20/3.86  tff(c_1782, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_235])).
% 10.20/3.86  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.20/3.86  tff(c_1970, plain, (![A_208, B_209, C_210]: (~r2_hidden('#skF_2'(A_208, B_209, C_210), B_209) | r2_hidden('#skF_3'(A_208, B_209, C_210), C_210) | k4_xboole_0(A_208, B_209)=C_210)), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.20/3.86  tff(c_1973, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_1970])).
% 10.20/3.86  tff(c_1978, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k1_xboole_0=C_8)), inference(demodulation, [status(thm), theory('equality')], [c_1782, c_1973])).
% 10.20/3.86  tff(c_70, plain, (![A_39, B_43]: (k1_relat_1('#skF_8'(A_39, B_43))=A_39 | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.20/3.86  tff(c_72, plain, (![A_39, B_43]: (v1_funct_1('#skF_8'(A_39, B_43)) | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.20/3.86  tff(c_74, plain, (![A_39, B_43]: (v1_relat_1('#skF_8'(A_39, B_43)) | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.20/3.86  tff(c_189, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(A_78, B_79), A_78) | r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.20/3.86  tff(c_42, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.20/3.86  tff(c_566, plain, (![A_131, B_132]: ('#skF_1'(k1_tarski(A_131), B_132)=A_131 | r1_tarski(k1_tarski(A_131), B_132))), inference(resolution, [status(thm)], [c_189, c_42])).
% 10.20/3.86  tff(c_266, plain, (![A_90, B_91]: (k2_relat_1('#skF_8'(A_90, B_91))=k1_tarski(B_91) | k1_xboole_0=A_90)), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.20/3.86  tff(c_76, plain, (![C_46]: (~r1_tarski(k2_relat_1(C_46), '#skF_9') | k1_relat_1(C_46)!='#skF_10' | ~v1_funct_1(C_46) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.20/3.86  tff(c_272, plain, (![B_91, A_90]: (~r1_tarski(k1_tarski(B_91), '#skF_9') | k1_relat_1('#skF_8'(A_90, B_91))!='#skF_10' | ~v1_funct_1('#skF_8'(A_90, B_91)) | ~v1_relat_1('#skF_8'(A_90, B_91)) | k1_xboole_0=A_90)), inference(superposition, [status(thm), theory('equality')], [c_266, c_76])).
% 10.20/3.86  tff(c_608, plain, (![A_141, A_142]: (k1_relat_1('#skF_8'(A_141, A_142))!='#skF_10' | ~v1_funct_1('#skF_8'(A_141, A_142)) | ~v1_relat_1('#skF_8'(A_141, A_142)) | k1_xboole_0=A_141 | '#skF_1'(k1_tarski(A_142), '#skF_9')=A_142)), inference(resolution, [status(thm)], [c_566, c_272])).
% 10.20/3.86  tff(c_953, plain, (![A_159, B_160]: (k1_relat_1('#skF_8'(A_159, B_160))!='#skF_10' | ~v1_funct_1('#skF_8'(A_159, B_160)) | '#skF_1'(k1_tarski(B_160), '#skF_9')=B_160 | k1_xboole_0=A_159)), inference(resolution, [status(thm)], [c_74, c_608])).
% 10.20/3.86  tff(c_3449, plain, (![A_284, B_285]: (k1_relat_1('#skF_8'(A_284, B_285))!='#skF_10' | '#skF_1'(k1_tarski(B_285), '#skF_9')=B_285 | k1_xboole_0=A_284)), inference(resolution, [status(thm)], [c_72, c_953])).
% 10.20/3.86  tff(c_3452, plain, (![A_39, B_43]: (A_39!='#skF_10' | '#skF_1'(k1_tarski(B_43), '#skF_9')=B_43 | k1_xboole_0=A_39 | k1_xboole_0=A_39)), inference(superposition, [status(thm), theory('equality')], [c_70, c_3449])).
% 10.20/3.86  tff(c_4047, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_3452])).
% 10.20/3.86  tff(c_32, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.20/3.86  tff(c_343, plain, (![A_97]: (k2_relat_1(A_97)=k1_xboole_0 | k1_relat_1(A_97)!=k1_xboole_0 | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.20/3.86  tff(c_349, plain, (![A_33]: (k2_relat_1('#skF_7'(A_33))=k1_xboole_0 | k1_relat_1('#skF_7'(A_33))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_343])).
% 10.20/3.86  tff(c_355, plain, (![A_99]: (k2_relat_1('#skF_7'(A_99))=k1_xboole_0 | k1_xboole_0!=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_349])).
% 10.20/3.86  tff(c_364, plain, (![A_99]: (~r1_tarski(k1_xboole_0, '#skF_9') | k1_relat_1('#skF_7'(A_99))!='#skF_10' | ~v1_funct_1('#skF_7'(A_99)) | ~v1_relat_1('#skF_7'(A_99)) | k1_xboole_0!=A_99)), inference(superposition, [status(thm), theory('equality')], [c_355, c_76])).
% 10.20/3.86  tff(c_371, plain, (![A_99]: (A_99!='#skF_10' | k1_xboole_0!=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_32, c_364])).
% 10.20/3.86  tff(c_376, plain, (k1_xboole_0!='#skF_10'), inference(reflexivity, [status(thm), theory('equality')], [c_371])).
% 10.20/3.86  tff(c_4101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4047, c_376])).
% 10.20/3.86  tff(c_4104, plain, (![B_299]: ('#skF_1'(k1_tarski(B_299), '#skF_9')=B_299)), inference(splitRight, [status(thm)], [c_3452])).
% 10.20/3.86  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.20/3.86  tff(c_4129, plain, (![B_300]: (~r2_hidden(B_300, '#skF_9') | r1_tarski(k1_tarski(B_300), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4104, c_4])).
% 10.20/3.86  tff(c_4344, plain, (![A_306, B_307]: (k1_relat_1('#skF_8'(A_306, B_307))!='#skF_10' | ~v1_funct_1('#skF_8'(A_306, B_307)) | ~v1_relat_1('#skF_8'(A_306, B_307)) | k1_xboole_0=A_306 | ~r2_hidden(B_307, '#skF_9'))), inference(resolution, [status(thm)], [c_4129, c_272])).
% 10.20/3.86  tff(c_27036, plain, (![A_12339, B_12340]: (k1_relat_1('#skF_8'(A_12339, B_12340))!='#skF_10' | ~v1_funct_1('#skF_8'(A_12339, B_12340)) | ~r2_hidden(B_12340, '#skF_9') | k1_xboole_0=A_12339)), inference(resolution, [status(thm)], [c_74, c_4344])).
% 10.20/3.86  tff(c_33146, plain, (![A_13781, B_13782]: (k1_relat_1('#skF_8'(A_13781, B_13782))!='#skF_10' | ~r2_hidden(B_13782, '#skF_9') | k1_xboole_0=A_13781)), inference(resolution, [status(thm)], [c_72, c_27036])).
% 10.20/3.86  tff(c_33151, plain, (![A_39, B_43]: (A_39!='#skF_10' | ~r2_hidden(B_43, '#skF_9') | k1_xboole_0=A_39 | k1_xboole_0=A_39)), inference(superposition, [status(thm), theory('equality')], [c_70, c_33146])).
% 10.20/3.86  tff(c_33153, plain, (![B_13812]: (~r2_hidden(B_13812, '#skF_9'))), inference(splitLeft, [status(thm)], [c_33151])).
% 10.20/3.86  tff(c_33209, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_1978, c_33153])).
% 10.20/3.86  tff(c_33257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_33209])).
% 10.20/3.86  tff(c_33259, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_33151])).
% 10.20/3.86  tff(c_33382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33259, c_376])).
% 10.20/3.86  tff(c_33384, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_78])).
% 10.20/3.86  tff(c_33383, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_78])).
% 10.20/3.86  tff(c_33391, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_33384, c_33383])).
% 10.20/3.86  tff(c_33385, plain, (![A_19]: (r1_tarski('#skF_10', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_33383, c_32])).
% 10.20/3.86  tff(c_33402, plain, (![A_19]: (r1_tarski('#skF_9', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_33391, c_33385])).
% 10.20/3.86  tff(c_58, plain, (![A_32]: (k2_relat_1(A_32)=k1_xboole_0 | k1_relat_1(A_32)!=k1_xboole_0 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.20/3.86  tff(c_33515, plain, (![A_13871]: (k2_relat_1(A_13871)='#skF_9' | k1_relat_1(A_13871)!='#skF_9' | ~v1_relat_1(A_13871))), inference(demodulation, [status(thm), theory('equality')], [c_33384, c_33384, c_58])).
% 10.20/3.86  tff(c_33521, plain, (![A_33]: (k2_relat_1('#skF_7'(A_33))='#skF_9' | k1_relat_1('#skF_7'(A_33))!='#skF_9')), inference(resolution, [status(thm)], [c_66, c_33515])).
% 10.20/3.86  tff(c_33526, plain, (![A_13872]: (k2_relat_1('#skF_7'(A_13872))='#skF_9' | A_13872!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_33521])).
% 10.20/3.86  tff(c_33410, plain, (![C_46]: (~r1_tarski(k2_relat_1(C_46), '#skF_9') | k1_relat_1(C_46)!='#skF_9' | ~v1_funct_1(C_46) | ~v1_relat_1(C_46))), inference(demodulation, [status(thm), theory('equality')], [c_33391, c_76])).
% 10.20/3.86  tff(c_33532, plain, (![A_13872]: (~r1_tarski('#skF_9', '#skF_9') | k1_relat_1('#skF_7'(A_13872))!='#skF_9' | ~v1_funct_1('#skF_7'(A_13872)) | ~v1_relat_1('#skF_7'(A_13872)) | A_13872!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_33526, c_33410])).
% 10.20/3.86  tff(c_33538, plain, (![A_13872]: (A_13872!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_33402, c_33532])).
% 10.20/3.86  tff(c_33386, plain, (![A_22]: (r1_xboole_0(A_22, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_33383, c_36])).
% 10.20/3.86  tff(c_33400, plain, (![A_22]: (r1_xboole_0(A_22, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_33391, c_33386])).
% 10.20/3.86  tff(c_33416, plain, (![B_13851, A_13852]: (r1_xboole_0(B_13851, A_13852) | ~r1_xboole_0(A_13852, B_13851))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.20/3.86  tff(c_33419, plain, (![A_22]: (r1_xboole_0('#skF_9', A_22))), inference(resolution, [status(thm)], [c_33400, c_33416])).
% 10.20/3.86  tff(c_33425, plain, (![A_13854, B_13855]: (k4_xboole_0(A_13854, B_13855)=A_13854 | ~r1_xboole_0(A_13854, B_13855))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.20/3.86  tff(c_33432, plain, (![A_22]: (k4_xboole_0('#skF_9', A_22)='#skF_9')), inference(resolution, [status(thm)], [c_33419, c_33425])).
% 10.20/3.86  tff(c_33581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33538, c_33432])).
% 10.20/3.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.20/3.86  
% 10.20/3.86  Inference rules
% 10.20/3.86  ----------------------
% 10.20/3.86  #Ref     : 1
% 10.20/3.86  #Sup     : 6566
% 10.20/3.86  #Fact    : 2
% 10.20/3.86  #Define  : 0
% 10.20/3.86  #Split   : 3
% 10.20/3.86  #Chain   : 0
% 10.20/3.86  #Close   : 0
% 10.20/3.86  
% 10.20/3.86  Ordering : KBO
% 10.20/3.86  
% 10.20/3.86  Simplification rules
% 10.20/3.86  ----------------------
% 10.20/3.86  #Subsume      : 2233
% 10.20/3.86  #Demod        : 1746
% 10.20/3.86  #Tautology    : 1451
% 10.20/3.86  #SimpNegUnit  : 123
% 10.20/3.86  #BackRed      : 197
% 10.20/3.86  
% 10.20/3.86  #Partial instantiations: 8664
% 10.20/3.86  #Strategies tried      : 1
% 10.20/3.86  
% 10.20/3.86  Timing (in seconds)
% 10.20/3.86  ----------------------
% 10.20/3.87  Preprocessing        : 0.32
% 10.20/3.87  Parsing              : 0.16
% 10.20/3.87  CNF conversion       : 0.03
% 10.20/3.87  Main loop            : 2.78
% 10.20/3.87  Inferencing          : 0.85
% 10.20/3.87  Reduction            : 0.88
% 10.20/3.87  Demodulation         : 0.61
% 10.20/3.87  BG Simplification    : 0.11
% 10.20/3.87  Subsumption          : 0.72
% 10.20/3.87  Abstraction          : 0.14
% 10.20/3.87  MUC search           : 0.00
% 10.20/3.87  Cooper               : 0.00
% 10.20/3.87  Total                : 3.13
% 10.20/3.87  Index Insertion      : 0.00
% 10.20/3.87  Index Deletion       : 0.00
% 10.20/3.87  Index Matching       : 0.00
% 10.20/3.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
