%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:30 EST 2020

% Result     : Theorem 4.30s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 273 expanded)
%              Number of leaves         :   37 ( 114 expanded)
%              Depth                    :   15
%              Number of atoms          :  112 ( 395 expanded)
%              Number of equality atoms :   45 ( 197 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_91,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_44,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    ! [A_23] : v1_funct_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_112,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_127,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_112])).

tff(c_147,plain,(
    ! [A_54] : k4_xboole_0(A_54,A_54) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_127])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_152,plain,(
    ! [A_54] : k4_xboole_0(A_54,k1_xboole_0) = k3_xboole_0(A_54,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_16])).

tff(c_164,plain,(
    ! [A_54] : k3_xboole_0(A_54,A_54) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_152])).

tff(c_489,plain,(
    ! [A_82,B_83] :
      ( k5_relat_1(k6_relat_1(A_82),B_83) = k7_relat_1(B_83,A_82)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [B_33,A_32] : k5_relat_1(k6_relat_1(B_33),k6_relat_1(A_32)) = k6_relat_1(k3_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_496,plain,(
    ! [A_32,A_82] :
      ( k7_relat_1(k6_relat_1(A_32),A_82) = k6_relat_1(k3_xboole_0(A_32,A_82))
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_42])).

tff(c_505,plain,(
    ! [A_32,A_82] : k7_relat_1(k6_relat_1(A_32),A_82) = k6_relat_1(k3_xboole_0(A_32,A_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_496])).

tff(c_28,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_519,plain,(
    ! [B_86,A_87] :
      ( k2_relat_1(k7_relat_1(B_86,A_87)) = k9_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_528,plain,(
    ! [A_32,A_82] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_32,A_82))) = k9_relat_1(k6_relat_1(A_32),A_82)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_519])).

tff(c_532,plain,(
    ! [A_32,A_82] : k9_relat_1(k6_relat_1(A_32),A_82) = k3_xboole_0(A_32,A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_528])).

tff(c_1051,plain,(
    ! [A_125,B_126] :
      ( k3_xboole_0(A_125,k9_relat_1(B_126,k1_relat_1(B_126))) = k9_relat_1(B_126,k10_relat_1(B_126,A_125))
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1136,plain,(
    ! [A_20,A_125] :
      ( k9_relat_1(k6_relat_1(A_20),k10_relat_1(k6_relat_1(A_20),A_125)) = k3_xboole_0(A_125,k9_relat_1(k6_relat_1(A_20),A_20))
      | ~ v1_funct_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1051])).

tff(c_1143,plain,(
    ! [A_127,A_128] : k3_xboole_0(A_127,k10_relat_1(k6_relat_1(A_127),A_128)) = k3_xboole_0(A_128,A_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_164,c_532,c_532,c_1136])).

tff(c_36,plain,(
    ! [A_24,C_26,B_25] :
      ( k3_xboole_0(A_24,k10_relat_1(C_26,B_25)) = k10_relat_1(k7_relat_1(C_26,A_24),B_25)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1159,plain,(
    ! [A_127,A_128] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_127),A_127),A_128) = k3_xboole_0(A_128,A_127)
      | ~ v1_relat_1(k6_relat_1(A_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_36])).

tff(c_1226,plain,(
    ! [A_127,A_128] : k10_relat_1(k6_relat_1(A_127),A_128) = k3_xboole_0(A_128,A_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_164,c_505,c_1159])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1524,plain,(
    ! [A_143,C_144,B_145] :
      ( r1_tarski(A_143,k10_relat_1(C_144,B_145))
      | ~ r1_tarski(k9_relat_1(C_144,A_143),B_145)
      | ~ r1_tarski(A_143,k1_relat_1(C_144))
      | ~ v1_funct_1(C_144)
      | ~ v1_relat_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2546,plain,(
    ! [A_187,C_188] :
      ( r1_tarski(A_187,k10_relat_1(C_188,k9_relat_1(C_188,A_187)))
      | ~ r1_tarski(A_187,k1_relat_1(C_188))
      | ~ v1_funct_1(C_188)
      | ~ v1_relat_1(C_188) ) ),
    inference(resolution,[status(thm)],[c_6,c_1524])).

tff(c_2572,plain,(
    ! [A_82,A_32] :
      ( r1_tarski(A_82,k10_relat_1(k6_relat_1(A_32),k3_xboole_0(A_32,A_82)))
      | ~ r1_tarski(A_82,k1_relat_1(k6_relat_1(A_32)))
      | ~ v1_funct_1(k6_relat_1(A_32))
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_2546])).

tff(c_3286,plain,(
    ! [A_216,A_217] :
      ( r1_tarski(A_216,k3_xboole_0(k3_xboole_0(A_217,A_216),A_217))
      | ~ r1_tarski(A_216,A_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_26,c_1226,c_2572])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_281,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(A_65,C_66)
      | ~ r1_tarski(B_67,C_66)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_297,plain,(
    ! [A_65,A_3,B_4] :
      ( r1_tarski(A_65,A_3)
      | ~ r1_tarski(A_65,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_281])).

tff(c_3356,plain,(
    ! [A_218,A_219] :
      ( r1_tarski(A_218,k3_xboole_0(A_219,A_218))
      | ~ r1_tarski(A_218,A_219) ) ),
    inference(resolution,[status(thm)],[c_3286,c_297])).

tff(c_1142,plain,(
    ! [A_20,A_125] : k3_xboole_0(A_20,k10_relat_1(k6_relat_1(A_20),A_125)) = k3_xboole_0(A_125,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_164,c_532,c_532,c_1136])).

tff(c_131,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_131])).

tff(c_1177,plain,(
    ! [A_127,A_128] :
      ( k3_xboole_0(A_127,k10_relat_1(k6_relat_1(A_127),A_128)) = A_127
      | ~ r1_tarski(A_127,k3_xboole_0(A_128,A_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_141])).

tff(c_1227,plain,(
    ! [A_128,A_127] :
      ( k3_xboole_0(A_128,A_127) = A_127
      | ~ r1_tarski(A_127,k3_xboole_0(A_128,A_127)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_1177])).

tff(c_3424,plain,(
    ! [A_220,A_221] :
      ( k3_xboole_0(A_220,A_221) = A_221
      | ~ r1_tarski(A_221,A_220) ) ),
    inference(resolution,[status(thm)],[c_3356,c_1227])).

tff(c_3569,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_3424])).

tff(c_3714,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3569,c_36])).

tff(c_3757,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3714])).

tff(c_3759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_3757])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:15:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.30/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.79  
% 4.30/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.79  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.30/1.79  
% 4.30/1.79  %Foreground sorts:
% 4.30/1.79  
% 4.30/1.79  
% 4.30/1.79  %Background operators:
% 4.30/1.79  
% 4.30/1.79  
% 4.30/1.79  %Foreground operators:
% 4.30/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.30/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.30/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.30/1.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.30/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.30/1.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.30/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.30/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.30/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.30/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.30/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.30/1.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.30/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.30/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.30/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.30/1.79  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.30/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.30/1.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.30/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.30/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.30/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.30/1.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.30/1.79  
% 4.30/1.81  tff(f_101, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 4.30/1.81  tff(f_69, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.30/1.81  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.30/1.81  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.30/1.81  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.30/1.81  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.30/1.81  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 4.30/1.81  tff(f_91, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 4.30/1.81  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.30/1.81  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 4.30/1.81  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 4.30/1.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.30/1.81  tff(f_89, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 4.30/1.81  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.30/1.81  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.30/1.81  tff(c_44, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.30/1.81  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.30/1.81  tff(c_46, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.30/1.81  tff(c_32, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.30/1.81  tff(c_34, plain, (![A_23]: (v1_funct_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.30/1.81  tff(c_26, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.30/1.81  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.30/1.81  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.30/1.81  tff(c_112, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.30/1.81  tff(c_127, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_112])).
% 4.30/1.81  tff(c_147, plain, (![A_54]: (k4_xboole_0(A_54, A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_127])).
% 4.30/1.81  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.30/1.81  tff(c_152, plain, (![A_54]: (k4_xboole_0(A_54, k1_xboole_0)=k3_xboole_0(A_54, A_54))), inference(superposition, [status(thm), theory('equality')], [c_147, c_16])).
% 4.30/1.81  tff(c_164, plain, (![A_54]: (k3_xboole_0(A_54, A_54)=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_152])).
% 4.30/1.81  tff(c_489, plain, (![A_82, B_83]: (k5_relat_1(k6_relat_1(A_82), B_83)=k7_relat_1(B_83, A_82) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.30/1.81  tff(c_42, plain, (![B_33, A_32]: (k5_relat_1(k6_relat_1(B_33), k6_relat_1(A_32))=k6_relat_1(k3_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.30/1.81  tff(c_496, plain, (![A_32, A_82]: (k7_relat_1(k6_relat_1(A_32), A_82)=k6_relat_1(k3_xboole_0(A_32, A_82)) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_489, c_42])).
% 4.30/1.81  tff(c_505, plain, (![A_32, A_82]: (k7_relat_1(k6_relat_1(A_32), A_82)=k6_relat_1(k3_xboole_0(A_32, A_82)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_496])).
% 4.30/1.81  tff(c_28, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.30/1.81  tff(c_519, plain, (![B_86, A_87]: (k2_relat_1(k7_relat_1(B_86, A_87))=k9_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.30/1.81  tff(c_528, plain, (![A_32, A_82]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_32, A_82)))=k9_relat_1(k6_relat_1(A_32), A_82) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_505, c_519])).
% 4.30/1.81  tff(c_532, plain, (![A_32, A_82]: (k9_relat_1(k6_relat_1(A_32), A_82)=k3_xboole_0(A_32, A_82))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_528])).
% 4.30/1.81  tff(c_1051, plain, (![A_125, B_126]: (k3_xboole_0(A_125, k9_relat_1(B_126, k1_relat_1(B_126)))=k9_relat_1(B_126, k10_relat_1(B_126, A_125)) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.30/1.81  tff(c_1136, plain, (![A_20, A_125]: (k9_relat_1(k6_relat_1(A_20), k10_relat_1(k6_relat_1(A_20), A_125))=k3_xboole_0(A_125, k9_relat_1(k6_relat_1(A_20), A_20)) | ~v1_funct_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1051])).
% 4.30/1.81  tff(c_1143, plain, (![A_127, A_128]: (k3_xboole_0(A_127, k10_relat_1(k6_relat_1(A_127), A_128))=k3_xboole_0(A_128, A_127))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_164, c_532, c_532, c_1136])).
% 4.30/1.81  tff(c_36, plain, (![A_24, C_26, B_25]: (k3_xboole_0(A_24, k10_relat_1(C_26, B_25))=k10_relat_1(k7_relat_1(C_26, A_24), B_25) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.30/1.81  tff(c_1159, plain, (![A_127, A_128]: (k10_relat_1(k7_relat_1(k6_relat_1(A_127), A_127), A_128)=k3_xboole_0(A_128, A_127) | ~v1_relat_1(k6_relat_1(A_127)))), inference(superposition, [status(thm), theory('equality')], [c_1143, c_36])).
% 4.30/1.81  tff(c_1226, plain, (![A_127, A_128]: (k10_relat_1(k6_relat_1(A_127), A_128)=k3_xboole_0(A_128, A_127))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_164, c_505, c_1159])).
% 4.30/1.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.30/1.81  tff(c_1524, plain, (![A_143, C_144, B_145]: (r1_tarski(A_143, k10_relat_1(C_144, B_145)) | ~r1_tarski(k9_relat_1(C_144, A_143), B_145) | ~r1_tarski(A_143, k1_relat_1(C_144)) | ~v1_funct_1(C_144) | ~v1_relat_1(C_144))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.30/1.81  tff(c_2546, plain, (![A_187, C_188]: (r1_tarski(A_187, k10_relat_1(C_188, k9_relat_1(C_188, A_187))) | ~r1_tarski(A_187, k1_relat_1(C_188)) | ~v1_funct_1(C_188) | ~v1_relat_1(C_188))), inference(resolution, [status(thm)], [c_6, c_1524])).
% 4.30/1.81  tff(c_2572, plain, (![A_82, A_32]: (r1_tarski(A_82, k10_relat_1(k6_relat_1(A_32), k3_xboole_0(A_32, A_82))) | ~r1_tarski(A_82, k1_relat_1(k6_relat_1(A_32))) | ~v1_funct_1(k6_relat_1(A_32)) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_532, c_2546])).
% 4.30/1.81  tff(c_3286, plain, (![A_216, A_217]: (r1_tarski(A_216, k3_xboole_0(k3_xboole_0(A_217, A_216), A_217)) | ~r1_tarski(A_216, A_217))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_26, c_1226, c_2572])).
% 4.30/1.81  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.30/1.81  tff(c_281, plain, (![A_65, C_66, B_67]: (r1_tarski(A_65, C_66) | ~r1_tarski(B_67, C_66) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.30/1.81  tff(c_297, plain, (![A_65, A_3, B_4]: (r1_tarski(A_65, A_3) | ~r1_tarski(A_65, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_281])).
% 4.30/1.81  tff(c_3356, plain, (![A_218, A_219]: (r1_tarski(A_218, k3_xboole_0(A_219, A_218)) | ~r1_tarski(A_218, A_219))), inference(resolution, [status(thm)], [c_3286, c_297])).
% 4.30/1.81  tff(c_1142, plain, (![A_20, A_125]: (k3_xboole_0(A_20, k10_relat_1(k6_relat_1(A_20), A_125))=k3_xboole_0(A_125, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_164, c_532, c_532, c_1136])).
% 4.30/1.81  tff(c_131, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.30/1.81  tff(c_141, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_131])).
% 4.30/1.81  tff(c_1177, plain, (![A_127, A_128]: (k3_xboole_0(A_127, k10_relat_1(k6_relat_1(A_127), A_128))=A_127 | ~r1_tarski(A_127, k3_xboole_0(A_128, A_127)))), inference(superposition, [status(thm), theory('equality')], [c_1143, c_141])).
% 4.30/1.81  tff(c_1227, plain, (![A_128, A_127]: (k3_xboole_0(A_128, A_127)=A_127 | ~r1_tarski(A_127, k3_xboole_0(A_128, A_127)))), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_1177])).
% 4.30/1.81  tff(c_3424, plain, (![A_220, A_221]: (k3_xboole_0(A_220, A_221)=A_221 | ~r1_tarski(A_221, A_220))), inference(resolution, [status(thm)], [c_3356, c_1227])).
% 4.30/1.81  tff(c_3569, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_3424])).
% 4.30/1.81  tff(c_3714, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3569, c_36])).
% 4.30/1.81  tff(c_3757, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3714])).
% 4.30/1.81  tff(c_3759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_3757])).
% 4.30/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.81  
% 4.30/1.81  Inference rules
% 4.30/1.81  ----------------------
% 4.30/1.81  #Ref     : 0
% 4.30/1.81  #Sup     : 843
% 4.30/1.81  #Fact    : 0
% 4.30/1.81  #Define  : 0
% 4.30/1.81  #Split   : 1
% 4.30/1.81  #Chain   : 0
% 4.30/1.81  #Close   : 0
% 4.30/1.81  
% 4.30/1.81  Ordering : KBO
% 4.30/1.81  
% 4.30/1.81  Simplification rules
% 4.30/1.81  ----------------------
% 4.30/1.81  #Subsume      : 52
% 4.30/1.81  #Demod        : 634
% 4.30/1.81  #Tautology    : 400
% 4.30/1.81  #SimpNegUnit  : 1
% 4.30/1.81  #BackRed      : 9
% 4.30/1.81  
% 4.30/1.81  #Partial instantiations: 0
% 4.30/1.81  #Strategies tried      : 1
% 4.30/1.81  
% 4.30/1.81  Timing (in seconds)
% 4.30/1.81  ----------------------
% 4.30/1.81  Preprocessing        : 0.31
% 4.30/1.81  Parsing              : 0.17
% 4.30/1.81  CNF conversion       : 0.02
% 4.30/1.81  Main loop            : 0.71
% 4.30/1.81  Inferencing          : 0.23
% 4.30/1.81  Reduction            : 0.27
% 4.30/1.81  Demodulation         : 0.21
% 4.30/1.81  BG Simplification    : 0.03
% 4.30/1.81  Subsumption          : 0.14
% 4.30/1.81  Abstraction          : 0.04
% 4.30/1.81  MUC search           : 0.00
% 4.30/1.81  Cooper               : 0.00
% 4.30/1.81  Total                : 1.06
% 4.30/1.81  Index Insertion      : 0.00
% 4.30/1.81  Index Deletion       : 0.00
% 4.30/1.81  Index Matching       : 0.00
% 4.30/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
