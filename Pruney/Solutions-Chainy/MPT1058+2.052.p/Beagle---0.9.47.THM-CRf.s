%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:28 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 202 expanded)
%              Number of leaves         :   37 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  120 ( 314 expanded)
%              Number of equality atoms :   42 ( 130 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_105,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_50,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_56,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_52,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_36,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [A_28] : k1_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_28] : k2_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_124,plain,(
    ! [A_63] :
      ( k10_relat_1(A_63,k2_relat_1(A_63)) = k1_relat_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_140,plain,(
    ! [A_28] :
      ( k10_relat_1(k6_relat_1(A_28),A_28) = k1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_124])).

tff(c_147,plain,(
    ! [A_28] : k10_relat_1(k6_relat_1(A_28),A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_140])).

tff(c_540,plain,(
    ! [B_111,A_112] : k5_relat_1(k6_relat_1(B_111),k6_relat_1(A_112)) = k6_relat_1(k3_xboole_0(A_112,B_111)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    ! [A_29,B_30] :
      ( k5_relat_1(k6_relat_1(A_29),B_30) = k7_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_546,plain,(
    ! [A_112,B_111] :
      ( k7_relat_1(k6_relat_1(A_112),B_111) = k6_relat_1(k3_xboole_0(A_112,B_111))
      | ~ v1_relat_1(k6_relat_1(A_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_34])).

tff(c_556,plain,(
    ! [A_112,B_111] : k7_relat_1(k6_relat_1(A_112),B_111) = k6_relat_1(k3_xboole_0(A_112,B_111)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_546])).

tff(c_790,plain,(
    ! [A_140,C_141,B_142] :
      ( k3_xboole_0(A_140,k10_relat_1(C_141,B_142)) = k10_relat_1(k7_relat_1(C_141,A_140),B_142)
      | ~ v1_relat_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_166,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_175,plain,(
    ! [A_65,B_66] : r1_tarski(k3_xboole_0(A_65,B_66),A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_12])).

tff(c_851,plain,(
    ! [C_143,A_144,B_145] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_143,A_144),B_145),A_144)
      | ~ v1_relat_1(C_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_175])).

tff(c_874,plain,(
    ! [A_112,B_111,B_145] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_112,B_111)),B_145),B_111)
      | ~ v1_relat_1(k6_relat_1(A_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_851])).

tff(c_887,plain,(
    ! [A_146,B_147,B_148] : r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_146,B_147)),B_148),B_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_874])).

tff(c_914,plain,(
    ! [A_146,B_147] : r1_tarski(k3_xboole_0(A_146,B_147),B_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_887])).

tff(c_560,plain,(
    ! [A_113,B_114] : k7_relat_1(k6_relat_1(A_113),B_114) = k6_relat_1(k3_xboole_0(A_113,B_114)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_546])).

tff(c_24,plain,(
    ! [B_24,A_23] :
      ( k2_relat_1(k7_relat_1(B_24,A_23)) = k9_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_566,plain,(
    ! [A_113,B_114] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_113,B_114))) = k9_relat_1(k6_relat_1(A_113),B_114)
      | ~ v1_relat_1(k6_relat_1(A_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_24])).

tff(c_572,plain,(
    ! [A_113,B_114] : k9_relat_1(k6_relat_1(A_113),B_114) = k3_xboole_0(A_113,B_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_566])).

tff(c_38,plain,(
    ! [A_31] : v1_funct_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1039,plain,(
    ! [B_159,A_160] :
      ( k9_relat_1(B_159,k10_relat_1(B_159,A_160)) = A_160
      | ~ r1_tarski(A_160,k2_relat_1(B_159))
      | ~ v1_funct_1(B_159)
      | ~ v1_relat_1(B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3677,plain,(
    ! [B_278] :
      ( k9_relat_1(B_278,k10_relat_1(B_278,k2_relat_1(B_278))) = k2_relat_1(B_278)
      | ~ v1_funct_1(B_278)
      | ~ v1_relat_1(B_278) ) ),
    inference(resolution,[status(thm)],[c_6,c_1039])).

tff(c_3703,plain,(
    ! [A_28] :
      ( k9_relat_1(k6_relat_1(A_28),k10_relat_1(k6_relat_1(A_28),A_28)) = k2_relat_1(k6_relat_1(A_28))
      | ~ v1_funct_1(k6_relat_1(A_28))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3677])).

tff(c_3711,plain,(
    ! [A_28] : k3_xboole_0(A_28,A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_572,c_147,c_32,c_3703])).

tff(c_1094,plain,(
    ! [A_28,A_160] :
      ( k9_relat_1(k6_relat_1(A_28),k10_relat_1(k6_relat_1(A_28),A_160)) = A_160
      | ~ r1_tarski(A_160,A_28)
      | ~ v1_funct_1(k6_relat_1(A_28))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1039])).

tff(c_8585,plain,(
    ! [A_397,A_398] :
      ( k3_xboole_0(A_397,k10_relat_1(k6_relat_1(A_397),A_398)) = A_398
      | ~ r1_tarski(A_398,A_397) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_572,c_1094])).

tff(c_40,plain,(
    ! [A_32,C_34,B_33] :
      ( k3_xboole_0(A_32,k10_relat_1(C_34,B_33)) = k10_relat_1(k7_relat_1(C_34,A_32),B_33)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8849,plain,(
    ! [A_397,A_398] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_397),A_397),A_398) = A_398
      | ~ v1_relat_1(k6_relat_1(A_397))
      | ~ r1_tarski(A_398,A_397) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8585,c_40])).

tff(c_8941,plain,(
    ! [A_399,A_400] :
      ( k10_relat_1(k6_relat_1(A_399),A_400) = A_400
      | ~ r1_tarski(A_400,A_399) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3711,c_556,c_8849])).

tff(c_2199,plain,(
    ! [A_205,C_206,B_207] :
      ( r1_tarski(A_205,k10_relat_1(C_206,B_207))
      | ~ r1_tarski(k9_relat_1(C_206,A_205),B_207)
      | ~ r1_tarski(A_205,k1_relat_1(C_206))
      | ~ v1_funct_1(C_206)
      | ~ v1_relat_1(C_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2209,plain,(
    ! [A_205,C_206] :
      ( r1_tarski(A_205,k10_relat_1(C_206,k9_relat_1(C_206,A_205)))
      | ~ r1_tarski(A_205,k1_relat_1(C_206))
      | ~ v1_funct_1(C_206)
      | ~ v1_relat_1(C_206) ) ),
    inference(resolution,[status(thm)],[c_6,c_2199])).

tff(c_8976,plain,(
    ! [A_205,A_399] :
      ( r1_tarski(A_205,k9_relat_1(k6_relat_1(A_399),A_205))
      | ~ r1_tarski(A_205,k1_relat_1(k6_relat_1(A_399)))
      | ~ v1_funct_1(k6_relat_1(A_399))
      | ~ v1_relat_1(k6_relat_1(A_399))
      | ~ r1_tarski(k9_relat_1(k6_relat_1(A_399),A_205),A_399) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8941,c_2209])).

tff(c_9298,plain,(
    ! [A_409,A_410] :
      ( r1_tarski(A_409,k3_xboole_0(A_410,A_409))
      | ~ r1_tarski(A_409,A_410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_572,c_36,c_38,c_30,c_572,c_8976])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9326,plain,(
    ! [A_410,A_409] :
      ( k3_xboole_0(A_410,A_409) = A_409
      | ~ r1_tarski(k3_xboole_0(A_410,A_409),A_409)
      | ~ r1_tarski(A_409,A_410) ) ),
    inference(resolution,[status(thm)],[c_9298,c_2])).

tff(c_9380,plain,(
    ! [A_411,A_412] :
      ( k3_xboole_0(A_411,A_412) = A_412
      | ~ r1_tarski(A_412,A_411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_9326])).

tff(c_9731,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_9380])).

tff(c_10340,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9731,c_40])).

tff(c_10418,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10340])).

tff(c_10420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_10418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:46:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.95/2.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.89  
% 7.95/2.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.89  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.95/2.89  
% 7.95/2.89  %Foreground sorts:
% 7.95/2.89  
% 7.95/2.89  
% 7.95/2.89  %Background operators:
% 7.95/2.89  
% 7.95/2.89  
% 7.95/2.89  %Foreground operators:
% 7.95/2.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.95/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.95/2.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.95/2.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.95/2.89  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.95/2.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.95/2.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.95/2.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.95/2.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.95/2.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.95/2.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.95/2.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.95/2.89  tff('#skF_2', type, '#skF_2': $i).
% 7.95/2.89  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.95/2.89  tff('#skF_3', type, '#skF_3': $i).
% 7.95/2.89  tff('#skF_1', type, '#skF_1': $i).
% 7.95/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.95/2.89  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.95/2.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.95/2.89  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.95/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.95/2.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.95/2.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.95/2.89  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.95/2.89  
% 7.95/2.91  tff(f_115, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 7.95/2.91  tff(f_75, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.95/2.91  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.95/2.91  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 7.95/2.91  tff(f_105, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 7.95/2.91  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 7.95/2.91  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 7.95/2.91  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.95/2.91  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.95/2.91  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 7.95/2.91  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.95/2.91  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 7.95/2.91  tff(f_103, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 7.95/2.91  tff(c_50, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.95/2.91  tff(c_56, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.95/2.91  tff(c_52, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.95/2.91  tff(c_36, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.95/2.91  tff(c_30, plain, (![A_28]: (k1_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.95/2.91  tff(c_32, plain, (![A_28]: (k2_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.95/2.91  tff(c_124, plain, (![A_63]: (k10_relat_1(A_63, k2_relat_1(A_63))=k1_relat_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.95/2.91  tff(c_140, plain, (![A_28]: (k10_relat_1(k6_relat_1(A_28), A_28)=k1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_124])).
% 7.95/2.91  tff(c_147, plain, (![A_28]: (k10_relat_1(k6_relat_1(A_28), A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_140])).
% 7.95/2.91  tff(c_540, plain, (![B_111, A_112]: (k5_relat_1(k6_relat_1(B_111), k6_relat_1(A_112))=k6_relat_1(k3_xboole_0(A_112, B_111)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.95/2.91  tff(c_34, plain, (![A_29, B_30]: (k5_relat_1(k6_relat_1(A_29), B_30)=k7_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.95/2.91  tff(c_546, plain, (![A_112, B_111]: (k7_relat_1(k6_relat_1(A_112), B_111)=k6_relat_1(k3_xboole_0(A_112, B_111)) | ~v1_relat_1(k6_relat_1(A_112)))), inference(superposition, [status(thm), theory('equality')], [c_540, c_34])).
% 7.95/2.91  tff(c_556, plain, (![A_112, B_111]: (k7_relat_1(k6_relat_1(A_112), B_111)=k6_relat_1(k3_xboole_0(A_112, B_111)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_546])).
% 7.95/2.91  tff(c_790, plain, (![A_140, C_141, B_142]: (k3_xboole_0(A_140, k10_relat_1(C_141, B_142))=k10_relat_1(k7_relat_1(C_141, A_140), B_142) | ~v1_relat_1(C_141))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.95/2.91  tff(c_166, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.95/2.91  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.95/2.91  tff(c_175, plain, (![A_65, B_66]: (r1_tarski(k3_xboole_0(A_65, B_66), A_65))), inference(superposition, [status(thm), theory('equality')], [c_166, c_12])).
% 7.95/2.91  tff(c_851, plain, (![C_143, A_144, B_145]: (r1_tarski(k10_relat_1(k7_relat_1(C_143, A_144), B_145), A_144) | ~v1_relat_1(C_143))), inference(superposition, [status(thm), theory('equality')], [c_790, c_175])).
% 7.95/2.91  tff(c_874, plain, (![A_112, B_111, B_145]: (r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_112, B_111)), B_145), B_111) | ~v1_relat_1(k6_relat_1(A_112)))), inference(superposition, [status(thm), theory('equality')], [c_556, c_851])).
% 7.95/2.91  tff(c_887, plain, (![A_146, B_147, B_148]: (r1_tarski(k10_relat_1(k6_relat_1(k3_xboole_0(A_146, B_147)), B_148), B_147))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_874])).
% 7.95/2.91  tff(c_914, plain, (![A_146, B_147]: (r1_tarski(k3_xboole_0(A_146, B_147), B_147))), inference(superposition, [status(thm), theory('equality')], [c_147, c_887])).
% 7.95/2.91  tff(c_560, plain, (![A_113, B_114]: (k7_relat_1(k6_relat_1(A_113), B_114)=k6_relat_1(k3_xboole_0(A_113, B_114)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_546])).
% 7.95/2.91  tff(c_24, plain, (![B_24, A_23]: (k2_relat_1(k7_relat_1(B_24, A_23))=k9_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.95/2.91  tff(c_566, plain, (![A_113, B_114]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_113, B_114)))=k9_relat_1(k6_relat_1(A_113), B_114) | ~v1_relat_1(k6_relat_1(A_113)))), inference(superposition, [status(thm), theory('equality')], [c_560, c_24])).
% 7.95/2.91  tff(c_572, plain, (![A_113, B_114]: (k9_relat_1(k6_relat_1(A_113), B_114)=k3_xboole_0(A_113, B_114))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_566])).
% 7.95/2.91  tff(c_38, plain, (![A_31]: (v1_funct_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.95/2.91  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.95/2.91  tff(c_1039, plain, (![B_159, A_160]: (k9_relat_1(B_159, k10_relat_1(B_159, A_160))=A_160 | ~r1_tarski(A_160, k2_relat_1(B_159)) | ~v1_funct_1(B_159) | ~v1_relat_1(B_159))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.95/2.91  tff(c_3677, plain, (![B_278]: (k9_relat_1(B_278, k10_relat_1(B_278, k2_relat_1(B_278)))=k2_relat_1(B_278) | ~v1_funct_1(B_278) | ~v1_relat_1(B_278))), inference(resolution, [status(thm)], [c_6, c_1039])).
% 7.95/2.91  tff(c_3703, plain, (![A_28]: (k9_relat_1(k6_relat_1(A_28), k10_relat_1(k6_relat_1(A_28), A_28))=k2_relat_1(k6_relat_1(A_28)) | ~v1_funct_1(k6_relat_1(A_28)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3677])).
% 7.95/2.91  tff(c_3711, plain, (![A_28]: (k3_xboole_0(A_28, A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_572, c_147, c_32, c_3703])).
% 7.95/2.91  tff(c_1094, plain, (![A_28, A_160]: (k9_relat_1(k6_relat_1(A_28), k10_relat_1(k6_relat_1(A_28), A_160))=A_160 | ~r1_tarski(A_160, A_28) | ~v1_funct_1(k6_relat_1(A_28)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1039])).
% 7.95/2.91  tff(c_8585, plain, (![A_397, A_398]: (k3_xboole_0(A_397, k10_relat_1(k6_relat_1(A_397), A_398))=A_398 | ~r1_tarski(A_398, A_397))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_572, c_1094])).
% 7.95/2.91  tff(c_40, plain, (![A_32, C_34, B_33]: (k3_xboole_0(A_32, k10_relat_1(C_34, B_33))=k10_relat_1(k7_relat_1(C_34, A_32), B_33) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.95/2.91  tff(c_8849, plain, (![A_397, A_398]: (k10_relat_1(k7_relat_1(k6_relat_1(A_397), A_397), A_398)=A_398 | ~v1_relat_1(k6_relat_1(A_397)) | ~r1_tarski(A_398, A_397))), inference(superposition, [status(thm), theory('equality')], [c_8585, c_40])).
% 7.95/2.91  tff(c_8941, plain, (![A_399, A_400]: (k10_relat_1(k6_relat_1(A_399), A_400)=A_400 | ~r1_tarski(A_400, A_399))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3711, c_556, c_8849])).
% 7.95/2.91  tff(c_2199, plain, (![A_205, C_206, B_207]: (r1_tarski(A_205, k10_relat_1(C_206, B_207)) | ~r1_tarski(k9_relat_1(C_206, A_205), B_207) | ~r1_tarski(A_205, k1_relat_1(C_206)) | ~v1_funct_1(C_206) | ~v1_relat_1(C_206))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.95/2.91  tff(c_2209, plain, (![A_205, C_206]: (r1_tarski(A_205, k10_relat_1(C_206, k9_relat_1(C_206, A_205))) | ~r1_tarski(A_205, k1_relat_1(C_206)) | ~v1_funct_1(C_206) | ~v1_relat_1(C_206))), inference(resolution, [status(thm)], [c_6, c_2199])).
% 7.95/2.91  tff(c_8976, plain, (![A_205, A_399]: (r1_tarski(A_205, k9_relat_1(k6_relat_1(A_399), A_205)) | ~r1_tarski(A_205, k1_relat_1(k6_relat_1(A_399))) | ~v1_funct_1(k6_relat_1(A_399)) | ~v1_relat_1(k6_relat_1(A_399)) | ~r1_tarski(k9_relat_1(k6_relat_1(A_399), A_205), A_399))), inference(superposition, [status(thm), theory('equality')], [c_8941, c_2209])).
% 7.95/2.91  tff(c_9298, plain, (![A_409, A_410]: (r1_tarski(A_409, k3_xboole_0(A_410, A_409)) | ~r1_tarski(A_409, A_410))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_572, c_36, c_38, c_30, c_572, c_8976])).
% 7.95/2.91  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.95/2.91  tff(c_9326, plain, (![A_410, A_409]: (k3_xboole_0(A_410, A_409)=A_409 | ~r1_tarski(k3_xboole_0(A_410, A_409), A_409) | ~r1_tarski(A_409, A_410))), inference(resolution, [status(thm)], [c_9298, c_2])).
% 7.95/2.91  tff(c_9380, plain, (![A_411, A_412]: (k3_xboole_0(A_411, A_412)=A_412 | ~r1_tarski(A_412, A_411))), inference(demodulation, [status(thm), theory('equality')], [c_914, c_9326])).
% 7.95/2.91  tff(c_9731, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_9380])).
% 7.95/2.91  tff(c_10340, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9731, c_40])).
% 7.95/2.91  tff(c_10418, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_10340])).
% 7.95/2.91  tff(c_10420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_10418])).
% 7.95/2.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.91  
% 7.95/2.91  Inference rules
% 7.95/2.91  ----------------------
% 7.95/2.91  #Ref     : 0
% 7.95/2.91  #Sup     : 2410
% 7.95/2.91  #Fact    : 0
% 7.95/2.91  #Define  : 0
% 7.95/2.91  #Split   : 1
% 7.95/2.91  #Chain   : 0
% 7.95/2.91  #Close   : 0
% 7.95/2.91  
% 7.95/2.91  Ordering : KBO
% 7.95/2.91  
% 7.95/2.91  Simplification rules
% 7.95/2.91  ----------------------
% 7.95/2.91  #Subsume      : 84
% 7.95/2.91  #Demod        : 1519
% 7.95/2.91  #Tautology    : 1134
% 7.95/2.91  #SimpNegUnit  : 1
% 7.95/2.91  #BackRed      : 1
% 7.95/2.91  
% 7.95/2.91  #Partial instantiations: 0
% 7.95/2.91  #Strategies tried      : 1
% 7.95/2.91  
% 7.95/2.91  Timing (in seconds)
% 7.95/2.91  ----------------------
% 7.95/2.91  Preprocessing        : 0.34
% 7.95/2.91  Parsing              : 0.19
% 7.95/2.91  CNF conversion       : 0.02
% 7.95/2.91  Main loop            : 1.80
% 7.95/2.91  Inferencing          : 0.46
% 7.95/2.91  Reduction            : 0.82
% 7.95/2.91  Demodulation         : 0.69
% 7.95/2.91  BG Simplification    : 0.06
% 7.95/2.91  Subsumption          : 0.36
% 7.95/2.91  Abstraction          : 0.08
% 7.95/2.91  MUC search           : 0.00
% 7.95/2.91  Cooper               : 0.00
% 7.95/2.91  Total                : 2.17
% 7.95/2.91  Index Insertion      : 0.00
% 7.95/2.91  Index Deletion       : 0.00
% 7.95/2.91  Index Matching       : 0.00
% 7.95/2.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
