%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:31 EST 2020

% Result     : Theorem 11.88s
% Output     : CNFRefutation 12.17s
% Verified   : 
% Statistics : Number of formulae       :  155 (1797 expanded)
%              Number of leaves         :   39 ( 644 expanded)
%              Depth                    :   19
%              Number of atoms          :  269 (3008 expanded)
%              Number of equality atoms :   94 (1119 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_53,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_84,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_22,plain,(
    ! [A_35] : v1_relat_1(k6_relat_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    ! [A_57,B_58] :
      ( k5_relat_1(k6_relat_1(A_57),B_58) = k7_relat_1(B_58,A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    ! [A_49] : k4_relat_1(k6_relat_1(A_49)) = k6_relat_1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1154,plain,(
    ! [B_142,A_143] :
      ( k5_relat_1(k4_relat_1(B_142),k4_relat_1(A_143)) = k4_relat_1(k5_relat_1(A_143,B_142))
      | ~ v1_relat_1(B_142)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1169,plain,(
    ! [A_49,A_143] :
      ( k5_relat_1(k6_relat_1(A_49),k4_relat_1(A_143)) = k4_relat_1(k5_relat_1(A_143,k6_relat_1(A_49)))
      | ~ v1_relat_1(k6_relat_1(A_49))
      | ~ v1_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1154])).

tff(c_2027,plain,(
    ! [A_194,A_195] :
      ( k5_relat_1(k6_relat_1(A_194),k4_relat_1(A_195)) = k4_relat_1(k5_relat_1(A_195,k6_relat_1(A_194)))
      | ~ v1_relat_1(A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1169])).

tff(c_2060,plain,(
    ! [A_49,A_194] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_49),k6_relat_1(A_194))) = k5_relat_1(k6_relat_1(A_194),k6_relat_1(A_49))
      | ~ v1_relat_1(k6_relat_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2027])).

tff(c_2121,plain,(
    ! [A_200,A_201] : k4_relat_1(k5_relat_1(k6_relat_1(A_200),k6_relat_1(A_201))) = k5_relat_1(k6_relat_1(A_201),k6_relat_1(A_200)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2060])).

tff(c_20,plain,(
    ! [A_33,B_34] :
      ( v1_relat_1(k5_relat_1(A_33,B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2046,plain,(
    ! [A_195,A_194] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_195,k6_relat_1(A_194))))
      | ~ v1_relat_1(k4_relat_1(A_195))
      | ~ v1_relat_1(k6_relat_1(A_194))
      | ~ v1_relat_1(A_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2027,c_20])).

tff(c_2067,plain,(
    ! [A_195,A_194] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_195,k6_relat_1(A_194))))
      | ~ v1_relat_1(k4_relat_1(A_195))
      | ~ v1_relat_1(A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2046])).

tff(c_2127,plain,(
    ! [A_201,A_200] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_201),k6_relat_1(A_200)))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(A_200)))
      | ~ v1_relat_1(k6_relat_1(A_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2121,c_2067])).

tff(c_2213,plain,(
    ! [A_204,A_205] : v1_relat_1(k5_relat_1(k6_relat_1(A_204),k6_relat_1(A_205))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_36,c_2127])).

tff(c_2225,plain,(
    ! [A_205,A_57] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_205),A_57))
      | ~ v1_relat_1(k6_relat_1(A_205)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2213])).

tff(c_2237,plain,(
    ! [A_205,A_57] : v1_relat_1(k7_relat_1(k6_relat_1(A_205),A_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2225])).

tff(c_32,plain,(
    ! [A_48] : k1_relat_1(k6_relat_1(A_48)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_48] : k2_relat_1(k6_relat_1(A_48)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_147,plain,(
    ! [A_79,B_80] :
      ( k5_relat_1(k6_relat_1(A_79),B_80) = k7_relat_1(B_80,A_79)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    ! [A_54] :
      ( k5_relat_1(A_54,k6_relat_1(k2_relat_1(A_54))) = A_54
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_158,plain,(
    ! [A_79] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_79))),A_79) = k6_relat_1(A_79)
      | ~ v1_relat_1(k6_relat_1(A_79))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_79)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_42])).

tff(c_179,plain,(
    ! [A_79] : k7_relat_1(k6_relat_1(A_79),A_79) = k6_relat_1(A_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_34,c_158])).

tff(c_233,plain,(
    ! [B_87,A_88] :
      ( k3_xboole_0(k1_relat_1(B_87),A_88) = k1_relat_1(k7_relat_1(B_87,A_88))
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_245,plain,(
    ! [A_48,A_88] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_48),A_88)) = k3_xboole_0(A_48,A_88)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_233])).

tff(c_250,plain,(
    ! [A_89,A_90] : k1_relat_1(k7_relat_1(k6_relat_1(A_89),A_90)) = k3_xboole_0(A_89,A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_245])).

tff(c_262,plain,(
    ! [A_79] : k3_xboole_0(A_79,A_79) = k1_relat_1(k6_relat_1(A_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_250])).

tff(c_265,plain,(
    ! [A_79] : k3_xboole_0(A_79,A_79) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_262])).

tff(c_249,plain,(
    ! [A_48,A_88] : k1_relat_1(k7_relat_1(k6_relat_1(A_48),A_88)) = k3_xboole_0(A_48,A_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_245])).

tff(c_2156,plain,(
    ! [A_201,A_57] :
      ( k5_relat_1(k6_relat_1(A_201),k6_relat_1(A_57)) = k4_relat_1(k7_relat_1(k6_relat_1(A_201),A_57))
      | ~ v1_relat_1(k6_relat_1(A_201)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2121])).

tff(c_2325,plain,(
    ! [A_210,A_211] : k5_relat_1(k6_relat_1(A_210),k6_relat_1(A_211)) = k4_relat_1(k7_relat_1(k6_relat_1(A_210),A_211)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2156])).

tff(c_2369,plain,(
    ! [A_57,A_211] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_57),A_211)) = k7_relat_1(k6_relat_1(A_211),A_57)
      | ~ v1_relat_1(k6_relat_1(A_211)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2325])).

tff(c_2399,plain,(
    ! [A_57,A_211] : k4_relat_1(k7_relat_1(k6_relat_1(A_57),A_211)) = k7_relat_1(k6_relat_1(A_211),A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2369])).

tff(c_105,plain,(
    ! [A_74] :
      ( k5_relat_1(A_74,k6_relat_1(k2_relat_1(A_74))) = A_74
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_117,plain,(
    ! [A_48] :
      ( k5_relat_1(k6_relat_1(A_48),k6_relat_1(A_48)) = k6_relat_1(A_48)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_105])).

tff(c_123,plain,(
    ! [A_48] : k5_relat_1(k6_relat_1(A_48),k6_relat_1(A_48)) = k6_relat_1(A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_1401,plain,(
    ! [B_158,C_159,A_160] :
      ( k7_relat_1(k5_relat_1(B_158,C_159),A_160) = k5_relat_1(k7_relat_1(B_158,A_160),C_159)
      | ~ v1_relat_1(C_159)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1449,plain,(
    ! [A_48,A_160] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_48),A_160),k6_relat_1(A_48)) = k7_relat_1(k6_relat_1(A_48),A_160)
      | ~ v1_relat_1(k6_relat_1(A_48))
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_1401])).

tff(c_1464,plain,(
    ! [A_48,A_160] : k5_relat_1(k7_relat_1(k6_relat_1(A_48),A_160),k6_relat_1(A_48)) = k7_relat_1(k6_relat_1(A_48),A_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_1449])).

tff(c_17749,plain,(
    ! [A_554,A_555] :
      ( k4_relat_1(k5_relat_1(A_554,k6_relat_1(A_555))) = k7_relat_1(k4_relat_1(A_554),A_555)
      | ~ v1_relat_1(A_554)
      | ~ v1_relat_1(k4_relat_1(A_554)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2027])).

tff(c_17851,plain,(
    ! [A_48,A_160] :
      ( k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_48),A_160)),A_48) = k4_relat_1(k7_relat_1(k6_relat_1(A_48),A_160))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_48),A_160))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_48),A_160))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1464,c_17749])).

tff(c_17896,plain,(
    ! [A_556,A_557] : k7_relat_1(k7_relat_1(k6_relat_1(A_556),A_557),A_557) = k7_relat_1(k6_relat_1(A_556),A_557) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_2399,c_2237,c_2399,c_2399,c_17851])).

tff(c_44,plain,(
    ! [B_56,A_55] :
      ( k3_xboole_0(k1_relat_1(B_56),A_55) = k1_relat_1(k7_relat_1(B_56,A_55))
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_286,plain,(
    ! [B_92,A_93] :
      ( k7_relat_1(B_92,A_93) = B_92
      | ~ r1_tarski(k1_relat_1(B_92),A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_292,plain,(
    ! [A_48,A_93] :
      ( k7_relat_1(k6_relat_1(A_48),A_93) = k6_relat_1(A_48)
      | ~ r1_tarski(A_48,A_93)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_286])).

tff(c_330,plain,(
    ! [A_96,A_97] :
      ( k7_relat_1(k6_relat_1(A_96),A_97) = k6_relat_1(A_96)
      | ~ r1_tarski(A_96,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_292])).

tff(c_340,plain,(
    ! [A_96,A_97] :
      ( k3_xboole_0(A_96,A_97) = k1_relat_1(k6_relat_1(A_96))
      | ~ r1_tarski(A_96,A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_249])).

tff(c_384,plain,(
    ! [A_98,A_99] :
      ( k3_xboole_0(A_98,A_99) = A_98
      | ~ r1_tarski(A_98,A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_340])).

tff(c_416,plain,(
    ! [A_102,B_103] : k3_xboole_0(k3_xboole_0(A_102,B_103),A_102) = k3_xboole_0(A_102,B_103) ),
    inference(resolution,[status(thm)],[c_2,c_384])).

tff(c_437,plain,(
    ! [B_56,A_55] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_56,A_55)),k1_relat_1(B_56)) = k3_xboole_0(k1_relat_1(B_56),A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_416])).

tff(c_17939,plain,(
    ! [A_556,A_557] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_556),A_557)),k1_relat_1(k7_relat_1(k6_relat_1(A_556),A_557))) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_556),A_557)),A_557)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_556),A_557)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17896,c_437])).

tff(c_18058,plain,(
    ! [A_556,A_557] : k3_xboole_0(k3_xboole_0(A_556,A_557),A_557) = k3_xboole_0(A_556,A_557) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_265,c_249,c_249,c_249,c_17939])).

tff(c_26,plain,(
    ! [B_41,A_40] :
      ( k2_relat_1(k7_relat_1(B_41,A_40)) = k9_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_595,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_110,B_111)),k2_relat_1(B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_607,plain,(
    ! [B_58,A_57] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_58,A_57)),k2_relat_1(B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(k6_relat_1(A_57))
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_595])).

tff(c_628,plain,(
    ! [B_112,A_113] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_112,A_113)),k2_relat_1(B_112))
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_607])).

tff(c_649,plain,(
    ! [A_48,A_113] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_48),A_113)),A_48)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_628])).

tff(c_658,plain,(
    ! [A_114,A_115] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_114),A_115)),A_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_649])).

tff(c_672,plain,(
    ! [A_114,A_40] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_114),A_40),A_114)
      | ~ v1_relat_1(k6_relat_1(A_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_658])).

tff(c_683,plain,(
    ! [A_116,A_117] : r1_tarski(k9_relat_1(k6_relat_1(A_116),A_117),A_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_672])).

tff(c_368,plain,(
    ! [A_96,A_97] :
      ( k3_xboole_0(A_96,A_97) = A_96
      | ~ r1_tarski(A_96,A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_340])).

tff(c_693,plain,(
    ! [A_116,A_117] : k3_xboole_0(k9_relat_1(k6_relat_1(A_116),A_117),A_116) = k9_relat_1(k6_relat_1(A_116),A_117) ),
    inference(resolution,[status(thm)],[c_683,c_368])).

tff(c_2808,plain,(
    ! [A_228,A_229] : k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_228),A_229)),A_228) = k2_relat_1(k7_relat_1(k6_relat_1(A_228),A_229)) ),
    inference(resolution,[status(thm)],[c_658,c_368])).

tff(c_2852,plain,(
    ! [A_228,A_40] :
      ( k3_xboole_0(k9_relat_1(k6_relat_1(A_228),A_40),A_228) = k2_relat_1(k7_relat_1(k6_relat_1(A_228),A_40))
      | ~ v1_relat_1(k6_relat_1(A_228)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2808])).

tff(c_2876,plain,(
    ! [A_228,A_40] : k2_relat_1(k7_relat_1(k6_relat_1(A_228),A_40)) = k9_relat_1(k6_relat_1(A_228),A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_693,c_2852])).

tff(c_266,plain,(
    ! [A_91] : k3_xboole_0(A_91,A_91) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_262])).

tff(c_276,plain,(
    ! [A_91] : r1_tarski(A_91,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_2])).

tff(c_480,plain,(
    ! [A_106,B_107] :
      ( k5_relat_1(k6_relat_1(A_106),B_107) = B_107
      | ~ r1_tarski(k1_relat_1(B_107),A_106)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_495,plain,(
    ! [B_107] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_107)),B_107) = B_107
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_276,c_480])).

tff(c_28,plain,(
    ! [A_42,B_44] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_42,B_44)),k2_relat_1(B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6701,plain,(
    ! [A_360,B_361] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_360,B_361))),k2_relat_1(k4_relat_1(A_360)))
      | ~ v1_relat_1(k4_relat_1(A_360))
      | ~ v1_relat_1(k4_relat_1(B_361))
      | ~ v1_relat_1(B_361)
      | ~ v1_relat_1(A_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_28])).

tff(c_6752,plain,(
    ! [B_107] :
      ( r1_tarski(k2_relat_1(k4_relat_1(B_107)),k2_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_107)))))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_107))))
      | ~ v1_relat_1(k4_relat_1(B_107))
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(B_107)))
      | ~ v1_relat_1(B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_6701])).

tff(c_7024,plain,(
    ! [B_363] :
      ( r1_tarski(k2_relat_1(k4_relat_1(B_363)),k1_relat_1(B_363))
      | ~ v1_relat_1(k4_relat_1(B_363))
      | ~ v1_relat_1(B_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_36,c_34,c_36,c_6752])).

tff(c_7049,plain,(
    ! [A_211,A_57] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_211),A_57)),k1_relat_1(k7_relat_1(k6_relat_1(A_57),A_211)))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_57),A_211)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_57),A_211)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2399,c_7024])).

tff(c_7078,plain,(
    ! [A_364,A_365] : r1_tarski(k9_relat_1(k6_relat_1(A_364),A_365),k3_xboole_0(A_365,A_364)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_2237,c_2399,c_2876,c_249,c_7049])).

tff(c_799,plain,(
    ! [B_122,A_123] :
      ( k5_relat_1(B_122,k6_relat_1(A_123)) = B_122
      | ~ r1_tarski(k2_relat_1(B_122),A_123)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_821,plain,(
    ! [A_48,A_123] :
      ( k5_relat_1(k6_relat_1(A_48),k6_relat_1(A_123)) = k6_relat_1(A_48)
      | ~ r1_tarski(A_48,A_123)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_799])).

tff(c_829,plain,(
    ! [A_124,A_125] :
      ( k5_relat_1(k6_relat_1(A_124),k6_relat_1(A_125)) = k6_relat_1(A_124)
      | ~ r1_tarski(A_124,A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_821])).

tff(c_848,plain,(
    ! [A_125,A_124] :
      ( k7_relat_1(k6_relat_1(A_125),A_124) = k6_relat_1(A_124)
      | ~ v1_relat_1(k6_relat_1(A_125))
      | ~ r1_tarski(A_124,A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_46])).

tff(c_912,plain,(
    ! [A_126,A_127] :
      ( k7_relat_1(k6_relat_1(A_126),A_127) = k6_relat_1(A_127)
      | ~ r1_tarski(A_127,A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_848])).

tff(c_947,plain,(
    ! [A_126,A_127] :
      ( k9_relat_1(k6_relat_1(A_126),A_127) = k2_relat_1(k6_relat_1(A_127))
      | ~ v1_relat_1(k6_relat_1(A_126))
      | ~ r1_tarski(A_127,A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_26])).

tff(c_979,plain,(
    ! [A_126,A_127] :
      ( k9_relat_1(k6_relat_1(A_126),A_127) = A_127
      | ~ r1_tarski(A_127,A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_34,c_947])).

tff(c_892,plain,(
    ! [A_125,A_124] :
      ( k7_relat_1(k6_relat_1(A_125),A_124) = k6_relat_1(A_124)
      | ~ r1_tarski(A_124,A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_848])).

tff(c_1446,plain,(
    ! [A_57,A_160,B_58] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_57),A_160),B_58) = k7_relat_1(k7_relat_1(B_58,A_57),A_160)
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(k6_relat_1(A_57))
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1401])).

tff(c_2878,plain,(
    ! [A_230,A_231,B_232] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_230),A_231),B_232) = k7_relat_1(k7_relat_1(B_232,A_230),A_231)
      | ~ v1_relat_1(B_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1446])).

tff(c_616,plain,(
    ! [A_110,A_48] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_110,k6_relat_1(A_48))),A_48)
      | ~ v1_relat_1(k6_relat_1(A_48))
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_595])).

tff(c_627,plain,(
    ! [A_110,A_48] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_110,k6_relat_1(A_48))),A_48)
      | ~ v1_relat_1(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_616])).

tff(c_2900,plain,(
    ! [A_48,A_230,A_231] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_48),A_230),A_231)),A_48)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_230),A_231))
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2878,c_627])).

tff(c_3250,plain,(
    ! [A_245,A_246,A_247] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_245),A_246),A_247)),A_245) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2237,c_2900])).

tff(c_3266,plain,(
    ! [A_124,A_247,A_125] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_124),A_247)),A_125)
      | ~ r1_tarski(A_124,A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_3250])).

tff(c_3337,plain,(
    ! [A_251,A_252,A_253] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_251),A_252),A_253)
      | ~ r1_tarski(A_251,A_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2876,c_3266])).

tff(c_3442,plain,(
    ! [A_256,A_257,A_258] :
      ( r1_tarski(A_256,A_257)
      | ~ r1_tarski(A_258,A_257)
      | ~ r1_tarski(A_256,A_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_3337])).

tff(c_3481,plain,(
    ! [A_256,A_1,B_2] :
      ( r1_tarski(A_256,A_1)
      | ~ r1_tarski(A_256,k3_xboole_0(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_2,c_3442])).

tff(c_7307,plain,(
    ! [A_367,A_368] : r1_tarski(k9_relat_1(k6_relat_1(A_367),A_368),A_368) ),
    inference(resolution,[status(thm)],[c_7078,c_3481])).

tff(c_7371,plain,(
    ! [A_367,A_368] : k3_xboole_0(k9_relat_1(k6_relat_1(A_367),A_368),A_368) = k9_relat_1(k6_relat_1(A_367),A_368) ),
    inference(resolution,[status(thm)],[c_7307,c_368])).

tff(c_681,plain,(
    ! [A_114,A_40] : r1_tarski(k9_relat_1(k6_relat_1(A_114),A_40),A_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_672])).

tff(c_493,plain,(
    ! [A_106,A_48] :
      ( k5_relat_1(k6_relat_1(A_106),k6_relat_1(A_48)) = k6_relat_1(A_48)
      | ~ r1_tarski(A_48,A_106)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_480])).

tff(c_497,plain,(
    ! [A_106,A_48] :
      ( k5_relat_1(k6_relat_1(A_106),k6_relat_1(A_48)) = k6_relat_1(A_48)
      | ~ r1_tarski(A_48,A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_493])).

tff(c_1436,plain,(
    ! [A_106,A_160,A_48] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_106),A_160),k6_relat_1(A_48)) = k7_relat_1(k6_relat_1(A_48),A_160)
      | ~ v1_relat_1(k6_relat_1(A_48))
      | ~ v1_relat_1(k6_relat_1(A_106))
      | ~ r1_tarski(A_48,A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_1401])).

tff(c_24641,plain,(
    ! [A_625,A_626,A_627] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_625),A_626),k6_relat_1(A_627)) = k7_relat_1(k6_relat_1(A_627),A_626)
      | ~ r1_tarski(A_627,A_625) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_1436])).

tff(c_198,plain,(
    ! [B_82,A_83] :
      ( k2_relat_1(k7_relat_1(B_82,A_83)) = k9_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_204,plain,(
    ! [B_82,A_83] :
      ( k5_relat_1(k7_relat_1(B_82,A_83),k6_relat_1(k9_relat_1(B_82,A_83))) = k7_relat_1(B_82,A_83)
      | ~ v1_relat_1(k7_relat_1(B_82,A_83))
      | ~ v1_relat_1(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_42])).

tff(c_24673,plain,(
    ! [A_625,A_626] :
      ( k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_625),A_626)),A_626) = k7_relat_1(k6_relat_1(A_625),A_626)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_625),A_626))
      | ~ v1_relat_1(k6_relat_1(A_625))
      | ~ r1_tarski(k9_relat_1(k6_relat_1(A_625),A_626),A_625) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24641,c_204])).

tff(c_24852,plain,(
    ! [A_628,A_629] : k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_628),A_629)),A_629) = k7_relat_1(k6_relat_1(A_628),A_629) ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_22,c_2237,c_24673])).

tff(c_18167,plain,(
    ! [A_561,A_562] : k3_xboole_0(k3_xboole_0(A_561,A_562),A_562) = k3_xboole_0(A_561,A_562) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2237,c_265,c_249,c_249,c_249,c_17939])).

tff(c_18410,plain,(
    ! [B_56,A_55] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_56,A_55)),A_55) = k3_xboole_0(k1_relat_1(B_56),A_55)
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_18167])).

tff(c_24879,plain,(
    ! [A_628,A_629] :
      ( k3_xboole_0(k1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_628),A_629))),A_629) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_628),A_629)),A_629)
      | ~ v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_628),A_629))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24852,c_18410])).

tff(c_25104,plain,(
    ! [A_628,A_629] : k9_relat_1(k6_relat_1(A_628),A_629) = k3_xboole_0(A_628,A_629) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18058,c_7371,c_249,c_32,c_24879])).

tff(c_7158,plain,(
    ! [A_364,A_365] : r1_tarski(k9_relat_1(k6_relat_1(A_364),A_365),A_365) ),
    inference(resolution,[status(thm)],[c_7078,c_3481])).

tff(c_294,plain,(
    ! [A_48,A_93] :
      ( k7_relat_1(k6_relat_1(A_48),A_93) = k6_relat_1(A_48)
      | ~ r1_tarski(A_48,A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_292])).

tff(c_25091,plain,(
    ! [A_628,A_93] :
      ( k6_relat_1(k9_relat_1(k6_relat_1(A_628),A_93)) = k7_relat_1(k6_relat_1(A_628),A_93)
      | ~ r1_tarski(k9_relat_1(k6_relat_1(A_628),A_93),A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_24852])).

tff(c_25192,plain,(
    ! [A_628,A_93] : k6_relat_1(k9_relat_1(k6_relat_1(A_628),A_93)) = k7_relat_1(k6_relat_1(A_628),A_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7158,c_25091])).

tff(c_31367,plain,(
    ! [A_628,A_93] : k7_relat_1(k6_relat_1(A_628),A_93) = k6_relat_1(k3_xboole_0(A_628,A_93)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25104,c_25192])).

tff(c_50,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_161,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_50])).

tff(c_181,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_161])).

tff(c_31421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31367,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.88/4.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/4.94  
% 11.88/4.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.88/4.94  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 11.88/4.94  
% 11.88/4.94  %Foreground sorts:
% 11.88/4.94  
% 11.88/4.94  
% 11.88/4.94  %Background operators:
% 11.88/4.94  
% 11.88/4.94  
% 11.88/4.94  %Foreground operators:
% 11.88/4.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.88/4.94  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.88/4.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.88/4.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.88/4.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.88/4.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.88/4.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.88/4.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.88/4.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.88/4.94  tff('#skF_2', type, '#skF_2': $i).
% 11.88/4.94  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.88/4.94  tff('#skF_1', type, '#skF_1': $i).
% 11.88/4.94  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.88/4.94  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.88/4.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.88/4.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.88/4.94  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.88/4.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.88/4.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.88/4.94  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.88/4.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.88/4.94  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 11.88/4.94  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.88/4.94  
% 12.17/4.96  tff(f_53, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 12.17/4.96  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 12.17/4.96  tff(f_84, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 12.17/4.96  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 12.17/4.96  tff(f_51, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 12.17/4.96  tff(f_82, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 12.17/4.96  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 12.17/4.96  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 12.17/4.96  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 12.17/4.96  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 12.17/4.96  tff(f_114, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 12.17/4.96  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 12.17/4.96  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 12.17/4.96  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 12.17/4.96  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 12.17/4.96  tff(f_117, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 12.17/4.96  tff(c_22, plain, (![A_35]: (v1_relat_1(k6_relat_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.17/4.96  tff(c_46, plain, (![A_57, B_58]: (k5_relat_1(k6_relat_1(A_57), B_58)=k7_relat_1(B_58, A_57) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.17/4.96  tff(c_36, plain, (![A_49]: (k4_relat_1(k6_relat_1(A_49))=k6_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.17/4.96  tff(c_1154, plain, (![B_142, A_143]: (k5_relat_1(k4_relat_1(B_142), k4_relat_1(A_143))=k4_relat_1(k5_relat_1(A_143, B_142)) | ~v1_relat_1(B_142) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.17/4.96  tff(c_1169, plain, (![A_49, A_143]: (k5_relat_1(k6_relat_1(A_49), k4_relat_1(A_143))=k4_relat_1(k5_relat_1(A_143, k6_relat_1(A_49))) | ~v1_relat_1(k6_relat_1(A_49)) | ~v1_relat_1(A_143))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1154])).
% 12.17/4.96  tff(c_2027, plain, (![A_194, A_195]: (k5_relat_1(k6_relat_1(A_194), k4_relat_1(A_195))=k4_relat_1(k5_relat_1(A_195, k6_relat_1(A_194))) | ~v1_relat_1(A_195))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1169])).
% 12.17/4.96  tff(c_2060, plain, (![A_49, A_194]: (k4_relat_1(k5_relat_1(k6_relat_1(A_49), k6_relat_1(A_194)))=k5_relat_1(k6_relat_1(A_194), k6_relat_1(A_49)) | ~v1_relat_1(k6_relat_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2027])).
% 12.17/4.96  tff(c_2121, plain, (![A_200, A_201]: (k4_relat_1(k5_relat_1(k6_relat_1(A_200), k6_relat_1(A_201)))=k5_relat_1(k6_relat_1(A_201), k6_relat_1(A_200)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2060])).
% 12.17/4.96  tff(c_20, plain, (![A_33, B_34]: (v1_relat_1(k5_relat_1(A_33, B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.17/4.96  tff(c_2046, plain, (![A_195, A_194]: (v1_relat_1(k4_relat_1(k5_relat_1(A_195, k6_relat_1(A_194)))) | ~v1_relat_1(k4_relat_1(A_195)) | ~v1_relat_1(k6_relat_1(A_194)) | ~v1_relat_1(A_195))), inference(superposition, [status(thm), theory('equality')], [c_2027, c_20])).
% 12.17/4.96  tff(c_2067, plain, (![A_195, A_194]: (v1_relat_1(k4_relat_1(k5_relat_1(A_195, k6_relat_1(A_194)))) | ~v1_relat_1(k4_relat_1(A_195)) | ~v1_relat_1(A_195))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2046])).
% 12.17/4.96  tff(c_2127, plain, (![A_201, A_200]: (v1_relat_1(k5_relat_1(k6_relat_1(A_201), k6_relat_1(A_200))) | ~v1_relat_1(k4_relat_1(k6_relat_1(A_200))) | ~v1_relat_1(k6_relat_1(A_200)))), inference(superposition, [status(thm), theory('equality')], [c_2121, c_2067])).
% 12.17/4.96  tff(c_2213, plain, (![A_204, A_205]: (v1_relat_1(k5_relat_1(k6_relat_1(A_204), k6_relat_1(A_205))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_36, c_2127])).
% 12.17/4.96  tff(c_2225, plain, (![A_205, A_57]: (v1_relat_1(k7_relat_1(k6_relat_1(A_205), A_57)) | ~v1_relat_1(k6_relat_1(A_205)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2213])).
% 12.17/4.96  tff(c_2237, plain, (![A_205, A_57]: (v1_relat_1(k7_relat_1(k6_relat_1(A_205), A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2225])).
% 12.17/4.96  tff(c_32, plain, (![A_48]: (k1_relat_1(k6_relat_1(A_48))=A_48)), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.17/4.96  tff(c_34, plain, (![A_48]: (k2_relat_1(k6_relat_1(A_48))=A_48)), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.17/4.96  tff(c_147, plain, (![A_79, B_80]: (k5_relat_1(k6_relat_1(A_79), B_80)=k7_relat_1(B_80, A_79) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_108])).
% 12.17/4.96  tff(c_42, plain, (![A_54]: (k5_relat_1(A_54, k6_relat_1(k2_relat_1(A_54)))=A_54 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.17/4.96  tff(c_158, plain, (![A_79]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_79))), A_79)=k6_relat_1(A_79) | ~v1_relat_1(k6_relat_1(A_79)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_79)))))), inference(superposition, [status(thm), theory('equality')], [c_147, c_42])).
% 12.17/4.96  tff(c_179, plain, (![A_79]: (k7_relat_1(k6_relat_1(A_79), A_79)=k6_relat_1(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_34, c_158])).
% 12.17/4.96  tff(c_233, plain, (![B_87, A_88]: (k3_xboole_0(k1_relat_1(B_87), A_88)=k1_relat_1(k7_relat_1(B_87, A_88)) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.17/4.96  tff(c_245, plain, (![A_48, A_88]: (k1_relat_1(k7_relat_1(k6_relat_1(A_48), A_88))=k3_xboole_0(A_48, A_88) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_233])).
% 12.17/4.96  tff(c_250, plain, (![A_89, A_90]: (k1_relat_1(k7_relat_1(k6_relat_1(A_89), A_90))=k3_xboole_0(A_89, A_90))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_245])).
% 12.17/4.96  tff(c_262, plain, (![A_79]: (k3_xboole_0(A_79, A_79)=k1_relat_1(k6_relat_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_250])).
% 12.17/4.96  tff(c_265, plain, (![A_79]: (k3_xboole_0(A_79, A_79)=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_262])).
% 12.17/4.96  tff(c_249, plain, (![A_48, A_88]: (k1_relat_1(k7_relat_1(k6_relat_1(A_48), A_88))=k3_xboole_0(A_48, A_88))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_245])).
% 12.17/4.96  tff(c_2156, plain, (![A_201, A_57]: (k5_relat_1(k6_relat_1(A_201), k6_relat_1(A_57))=k4_relat_1(k7_relat_1(k6_relat_1(A_201), A_57)) | ~v1_relat_1(k6_relat_1(A_201)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2121])).
% 12.17/4.96  tff(c_2325, plain, (![A_210, A_211]: (k5_relat_1(k6_relat_1(A_210), k6_relat_1(A_211))=k4_relat_1(k7_relat_1(k6_relat_1(A_210), A_211)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2156])).
% 12.17/4.96  tff(c_2369, plain, (![A_57, A_211]: (k4_relat_1(k7_relat_1(k6_relat_1(A_57), A_211))=k7_relat_1(k6_relat_1(A_211), A_57) | ~v1_relat_1(k6_relat_1(A_211)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2325])).
% 12.17/4.96  tff(c_2399, plain, (![A_57, A_211]: (k4_relat_1(k7_relat_1(k6_relat_1(A_57), A_211))=k7_relat_1(k6_relat_1(A_211), A_57))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2369])).
% 12.17/4.96  tff(c_105, plain, (![A_74]: (k5_relat_1(A_74, k6_relat_1(k2_relat_1(A_74)))=A_74 | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.17/4.96  tff(c_117, plain, (![A_48]: (k5_relat_1(k6_relat_1(A_48), k6_relat_1(A_48))=k6_relat_1(A_48) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_105])).
% 12.17/4.96  tff(c_123, plain, (![A_48]: (k5_relat_1(k6_relat_1(A_48), k6_relat_1(A_48))=k6_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_117])).
% 12.17/4.96  tff(c_1401, plain, (![B_158, C_159, A_160]: (k7_relat_1(k5_relat_1(B_158, C_159), A_160)=k5_relat_1(k7_relat_1(B_158, A_160), C_159) | ~v1_relat_1(C_159) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.17/4.96  tff(c_1449, plain, (![A_48, A_160]: (k5_relat_1(k7_relat_1(k6_relat_1(A_48), A_160), k6_relat_1(A_48))=k7_relat_1(k6_relat_1(A_48), A_160) | ~v1_relat_1(k6_relat_1(A_48)) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_1401])).
% 12.17/4.96  tff(c_1464, plain, (![A_48, A_160]: (k5_relat_1(k7_relat_1(k6_relat_1(A_48), A_160), k6_relat_1(A_48))=k7_relat_1(k6_relat_1(A_48), A_160))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_1449])).
% 12.17/4.96  tff(c_17749, plain, (![A_554, A_555]: (k4_relat_1(k5_relat_1(A_554, k6_relat_1(A_555)))=k7_relat_1(k4_relat_1(A_554), A_555) | ~v1_relat_1(A_554) | ~v1_relat_1(k4_relat_1(A_554)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2027])).
% 12.17/4.96  tff(c_17851, plain, (![A_48, A_160]: (k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_48), A_160)), A_48)=k4_relat_1(k7_relat_1(k6_relat_1(A_48), A_160)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_48), A_160)) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_48), A_160))))), inference(superposition, [status(thm), theory('equality')], [c_1464, c_17749])).
% 12.17/4.96  tff(c_17896, plain, (![A_556, A_557]: (k7_relat_1(k7_relat_1(k6_relat_1(A_556), A_557), A_557)=k7_relat_1(k6_relat_1(A_556), A_557))), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_2399, c_2237, c_2399, c_2399, c_17851])).
% 12.17/4.96  tff(c_44, plain, (![B_56, A_55]: (k3_xboole_0(k1_relat_1(B_56), A_55)=k1_relat_1(k7_relat_1(B_56, A_55)) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_104])).
% 12.17/4.96  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.17/4.96  tff(c_286, plain, (![B_92, A_93]: (k7_relat_1(B_92, A_93)=B_92 | ~r1_tarski(k1_relat_1(B_92), A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_114])).
% 12.17/4.96  tff(c_292, plain, (![A_48, A_93]: (k7_relat_1(k6_relat_1(A_48), A_93)=k6_relat_1(A_48) | ~r1_tarski(A_48, A_93) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_286])).
% 12.17/4.96  tff(c_330, plain, (![A_96, A_97]: (k7_relat_1(k6_relat_1(A_96), A_97)=k6_relat_1(A_96) | ~r1_tarski(A_96, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_292])).
% 12.17/4.96  tff(c_340, plain, (![A_96, A_97]: (k3_xboole_0(A_96, A_97)=k1_relat_1(k6_relat_1(A_96)) | ~r1_tarski(A_96, A_97))), inference(superposition, [status(thm), theory('equality')], [c_330, c_249])).
% 12.17/4.96  tff(c_384, plain, (![A_98, A_99]: (k3_xboole_0(A_98, A_99)=A_98 | ~r1_tarski(A_98, A_99))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_340])).
% 12.17/4.96  tff(c_416, plain, (![A_102, B_103]: (k3_xboole_0(k3_xboole_0(A_102, B_103), A_102)=k3_xboole_0(A_102, B_103))), inference(resolution, [status(thm)], [c_2, c_384])).
% 12.17/4.96  tff(c_437, plain, (![B_56, A_55]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_56, A_55)), k1_relat_1(B_56))=k3_xboole_0(k1_relat_1(B_56), A_55) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_44, c_416])).
% 12.17/4.96  tff(c_17939, plain, (![A_556, A_557]: (k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_556), A_557)), k1_relat_1(k7_relat_1(k6_relat_1(A_556), A_557)))=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_556), A_557)), A_557) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_556), A_557)))), inference(superposition, [status(thm), theory('equality')], [c_17896, c_437])).
% 12.17/4.96  tff(c_18058, plain, (![A_556, A_557]: (k3_xboole_0(k3_xboole_0(A_556, A_557), A_557)=k3_xboole_0(A_556, A_557))), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_265, c_249, c_249, c_249, c_17939])).
% 12.17/4.96  tff(c_26, plain, (![B_41, A_40]: (k2_relat_1(k7_relat_1(B_41, A_40))=k9_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.17/4.96  tff(c_595, plain, (![A_110, B_111]: (r1_tarski(k2_relat_1(k5_relat_1(A_110, B_111)), k2_relat_1(B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.17/4.96  tff(c_607, plain, (![B_58, A_57]: (r1_tarski(k2_relat_1(k7_relat_1(B_58, A_57)), k2_relat_1(B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(k6_relat_1(A_57)) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_46, c_595])).
% 12.17/4.96  tff(c_628, plain, (![B_112, A_113]: (r1_tarski(k2_relat_1(k7_relat_1(B_112, A_113)), k2_relat_1(B_112)) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_607])).
% 12.17/4.96  tff(c_649, plain, (![A_48, A_113]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_48), A_113)), A_48) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_628])).
% 12.17/4.96  tff(c_658, plain, (![A_114, A_115]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_114), A_115)), A_114))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_649])).
% 12.17/4.97  tff(c_672, plain, (![A_114, A_40]: (r1_tarski(k9_relat_1(k6_relat_1(A_114), A_40), A_114) | ~v1_relat_1(k6_relat_1(A_114)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_658])).
% 12.17/4.97  tff(c_683, plain, (![A_116, A_117]: (r1_tarski(k9_relat_1(k6_relat_1(A_116), A_117), A_116))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_672])).
% 12.17/4.97  tff(c_368, plain, (![A_96, A_97]: (k3_xboole_0(A_96, A_97)=A_96 | ~r1_tarski(A_96, A_97))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_340])).
% 12.17/4.97  tff(c_693, plain, (![A_116, A_117]: (k3_xboole_0(k9_relat_1(k6_relat_1(A_116), A_117), A_116)=k9_relat_1(k6_relat_1(A_116), A_117))), inference(resolution, [status(thm)], [c_683, c_368])).
% 12.17/4.97  tff(c_2808, plain, (![A_228, A_229]: (k3_xboole_0(k2_relat_1(k7_relat_1(k6_relat_1(A_228), A_229)), A_228)=k2_relat_1(k7_relat_1(k6_relat_1(A_228), A_229)))), inference(resolution, [status(thm)], [c_658, c_368])).
% 12.17/4.97  tff(c_2852, plain, (![A_228, A_40]: (k3_xboole_0(k9_relat_1(k6_relat_1(A_228), A_40), A_228)=k2_relat_1(k7_relat_1(k6_relat_1(A_228), A_40)) | ~v1_relat_1(k6_relat_1(A_228)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2808])).
% 12.17/4.97  tff(c_2876, plain, (![A_228, A_40]: (k2_relat_1(k7_relat_1(k6_relat_1(A_228), A_40))=k9_relat_1(k6_relat_1(A_228), A_40))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_693, c_2852])).
% 12.17/4.97  tff(c_266, plain, (![A_91]: (k3_xboole_0(A_91, A_91)=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_262])).
% 12.17/4.97  tff(c_276, plain, (![A_91]: (r1_tarski(A_91, A_91))), inference(superposition, [status(thm), theory('equality')], [c_266, c_2])).
% 12.17/4.97  tff(c_480, plain, (![A_106, B_107]: (k5_relat_1(k6_relat_1(A_106), B_107)=B_107 | ~r1_tarski(k1_relat_1(B_107), A_106) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.17/4.97  tff(c_495, plain, (![B_107]: (k5_relat_1(k6_relat_1(k1_relat_1(B_107)), B_107)=B_107 | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_276, c_480])).
% 12.17/4.97  tff(c_28, plain, (![A_42, B_44]: (r1_tarski(k2_relat_1(k5_relat_1(A_42, B_44)), k2_relat_1(B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.17/4.97  tff(c_6701, plain, (![A_360, B_361]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_360, B_361))), k2_relat_1(k4_relat_1(A_360))) | ~v1_relat_1(k4_relat_1(A_360)) | ~v1_relat_1(k4_relat_1(B_361)) | ~v1_relat_1(B_361) | ~v1_relat_1(A_360))), inference(superposition, [status(thm), theory('equality')], [c_1154, c_28])).
% 12.17/4.97  tff(c_6752, plain, (![B_107]: (r1_tarski(k2_relat_1(k4_relat_1(B_107)), k2_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_107))))) | ~v1_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(B_107)))) | ~v1_relat_1(k4_relat_1(B_107)) | ~v1_relat_1(B_107) | ~v1_relat_1(k6_relat_1(k1_relat_1(B_107))) | ~v1_relat_1(B_107))), inference(superposition, [status(thm), theory('equality')], [c_495, c_6701])).
% 12.17/4.97  tff(c_7024, plain, (![B_363]: (r1_tarski(k2_relat_1(k4_relat_1(B_363)), k1_relat_1(B_363)) | ~v1_relat_1(k4_relat_1(B_363)) | ~v1_relat_1(B_363))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_36, c_34, c_36, c_6752])).
% 12.17/4.97  tff(c_7049, plain, (![A_211, A_57]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_211), A_57)), k1_relat_1(k7_relat_1(k6_relat_1(A_57), A_211))) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_57), A_211))) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_57), A_211)))), inference(superposition, [status(thm), theory('equality')], [c_2399, c_7024])).
% 12.17/4.97  tff(c_7078, plain, (![A_364, A_365]: (r1_tarski(k9_relat_1(k6_relat_1(A_364), A_365), k3_xboole_0(A_365, A_364)))), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_2237, c_2399, c_2876, c_249, c_7049])).
% 12.17/4.97  tff(c_799, plain, (![B_122, A_123]: (k5_relat_1(B_122, k6_relat_1(A_123))=B_122 | ~r1_tarski(k2_relat_1(B_122), A_123) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.17/4.97  tff(c_821, plain, (![A_48, A_123]: (k5_relat_1(k6_relat_1(A_48), k6_relat_1(A_123))=k6_relat_1(A_48) | ~r1_tarski(A_48, A_123) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_799])).
% 12.17/4.97  tff(c_829, plain, (![A_124, A_125]: (k5_relat_1(k6_relat_1(A_124), k6_relat_1(A_125))=k6_relat_1(A_124) | ~r1_tarski(A_124, A_125))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_821])).
% 12.17/4.97  tff(c_848, plain, (![A_125, A_124]: (k7_relat_1(k6_relat_1(A_125), A_124)=k6_relat_1(A_124) | ~v1_relat_1(k6_relat_1(A_125)) | ~r1_tarski(A_124, A_125))), inference(superposition, [status(thm), theory('equality')], [c_829, c_46])).
% 12.17/4.97  tff(c_912, plain, (![A_126, A_127]: (k7_relat_1(k6_relat_1(A_126), A_127)=k6_relat_1(A_127) | ~r1_tarski(A_127, A_126))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_848])).
% 12.17/4.97  tff(c_947, plain, (![A_126, A_127]: (k9_relat_1(k6_relat_1(A_126), A_127)=k2_relat_1(k6_relat_1(A_127)) | ~v1_relat_1(k6_relat_1(A_126)) | ~r1_tarski(A_127, A_126))), inference(superposition, [status(thm), theory('equality')], [c_912, c_26])).
% 12.17/4.97  tff(c_979, plain, (![A_126, A_127]: (k9_relat_1(k6_relat_1(A_126), A_127)=A_127 | ~r1_tarski(A_127, A_126))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_34, c_947])).
% 12.17/4.97  tff(c_892, plain, (![A_125, A_124]: (k7_relat_1(k6_relat_1(A_125), A_124)=k6_relat_1(A_124) | ~r1_tarski(A_124, A_125))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_848])).
% 12.17/4.97  tff(c_1446, plain, (![A_57, A_160, B_58]: (k5_relat_1(k7_relat_1(k6_relat_1(A_57), A_160), B_58)=k7_relat_1(k7_relat_1(B_58, A_57), A_160) | ~v1_relat_1(B_58) | ~v1_relat_1(k6_relat_1(A_57)) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1401])).
% 12.17/4.97  tff(c_2878, plain, (![A_230, A_231, B_232]: (k5_relat_1(k7_relat_1(k6_relat_1(A_230), A_231), B_232)=k7_relat_1(k7_relat_1(B_232, A_230), A_231) | ~v1_relat_1(B_232))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1446])).
% 12.17/4.97  tff(c_616, plain, (![A_110, A_48]: (r1_tarski(k2_relat_1(k5_relat_1(A_110, k6_relat_1(A_48))), A_48) | ~v1_relat_1(k6_relat_1(A_48)) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_34, c_595])).
% 12.17/4.97  tff(c_627, plain, (![A_110, A_48]: (r1_tarski(k2_relat_1(k5_relat_1(A_110, k6_relat_1(A_48))), A_48) | ~v1_relat_1(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_616])).
% 12.17/4.97  tff(c_2900, plain, (![A_48, A_230, A_231]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_48), A_230), A_231)), A_48) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_230), A_231)) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_2878, c_627])).
% 12.17/4.97  tff(c_3250, plain, (![A_245, A_246, A_247]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_245), A_246), A_247)), A_245))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2237, c_2900])).
% 12.17/4.97  tff(c_3266, plain, (![A_124, A_247, A_125]: (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(A_124), A_247)), A_125) | ~r1_tarski(A_124, A_125))), inference(superposition, [status(thm), theory('equality')], [c_892, c_3250])).
% 12.17/4.97  tff(c_3337, plain, (![A_251, A_252, A_253]: (r1_tarski(k9_relat_1(k6_relat_1(A_251), A_252), A_253) | ~r1_tarski(A_251, A_253))), inference(demodulation, [status(thm), theory('equality')], [c_2876, c_3266])).
% 12.17/4.97  tff(c_3442, plain, (![A_256, A_257, A_258]: (r1_tarski(A_256, A_257) | ~r1_tarski(A_258, A_257) | ~r1_tarski(A_256, A_258))), inference(superposition, [status(thm), theory('equality')], [c_979, c_3337])).
% 12.17/4.97  tff(c_3481, plain, (![A_256, A_1, B_2]: (r1_tarski(A_256, A_1) | ~r1_tarski(A_256, k3_xboole_0(A_1, B_2)))), inference(resolution, [status(thm)], [c_2, c_3442])).
% 12.17/4.97  tff(c_7307, plain, (![A_367, A_368]: (r1_tarski(k9_relat_1(k6_relat_1(A_367), A_368), A_368))), inference(resolution, [status(thm)], [c_7078, c_3481])).
% 12.17/4.97  tff(c_7371, plain, (![A_367, A_368]: (k3_xboole_0(k9_relat_1(k6_relat_1(A_367), A_368), A_368)=k9_relat_1(k6_relat_1(A_367), A_368))), inference(resolution, [status(thm)], [c_7307, c_368])).
% 12.17/4.97  tff(c_681, plain, (![A_114, A_40]: (r1_tarski(k9_relat_1(k6_relat_1(A_114), A_40), A_114))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_672])).
% 12.17/4.97  tff(c_493, plain, (![A_106, A_48]: (k5_relat_1(k6_relat_1(A_106), k6_relat_1(A_48))=k6_relat_1(A_48) | ~r1_tarski(A_48, A_106) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_480])).
% 12.17/4.97  tff(c_497, plain, (![A_106, A_48]: (k5_relat_1(k6_relat_1(A_106), k6_relat_1(A_48))=k6_relat_1(A_48) | ~r1_tarski(A_48, A_106))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_493])).
% 12.17/4.97  tff(c_1436, plain, (![A_106, A_160, A_48]: (k5_relat_1(k7_relat_1(k6_relat_1(A_106), A_160), k6_relat_1(A_48))=k7_relat_1(k6_relat_1(A_48), A_160) | ~v1_relat_1(k6_relat_1(A_48)) | ~v1_relat_1(k6_relat_1(A_106)) | ~r1_tarski(A_48, A_106))), inference(superposition, [status(thm), theory('equality')], [c_497, c_1401])).
% 12.17/4.97  tff(c_24641, plain, (![A_625, A_626, A_627]: (k5_relat_1(k7_relat_1(k6_relat_1(A_625), A_626), k6_relat_1(A_627))=k7_relat_1(k6_relat_1(A_627), A_626) | ~r1_tarski(A_627, A_625))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_1436])).
% 12.17/4.97  tff(c_198, plain, (![B_82, A_83]: (k2_relat_1(k7_relat_1(B_82, A_83))=k9_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.17/4.97  tff(c_204, plain, (![B_82, A_83]: (k5_relat_1(k7_relat_1(B_82, A_83), k6_relat_1(k9_relat_1(B_82, A_83)))=k7_relat_1(B_82, A_83) | ~v1_relat_1(k7_relat_1(B_82, A_83)) | ~v1_relat_1(B_82))), inference(superposition, [status(thm), theory('equality')], [c_198, c_42])).
% 12.17/4.97  tff(c_24673, plain, (![A_625, A_626]: (k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_625), A_626)), A_626)=k7_relat_1(k6_relat_1(A_625), A_626) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_625), A_626)) | ~v1_relat_1(k6_relat_1(A_625)) | ~r1_tarski(k9_relat_1(k6_relat_1(A_625), A_626), A_625))), inference(superposition, [status(thm), theory('equality')], [c_24641, c_204])).
% 12.17/4.97  tff(c_24852, plain, (![A_628, A_629]: (k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_628), A_629)), A_629)=k7_relat_1(k6_relat_1(A_628), A_629))), inference(demodulation, [status(thm), theory('equality')], [c_681, c_22, c_2237, c_24673])).
% 12.17/4.97  tff(c_18167, plain, (![A_561, A_562]: (k3_xboole_0(k3_xboole_0(A_561, A_562), A_562)=k3_xboole_0(A_561, A_562))), inference(demodulation, [status(thm), theory('equality')], [c_2237, c_265, c_249, c_249, c_249, c_17939])).
% 12.17/4.97  tff(c_18410, plain, (![B_56, A_55]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_56, A_55)), A_55)=k3_xboole_0(k1_relat_1(B_56), A_55) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_44, c_18167])).
% 12.17/4.97  tff(c_24879, plain, (![A_628, A_629]: (k3_xboole_0(k1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_628), A_629))), A_629)=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_628), A_629)), A_629) | ~v1_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(A_628), A_629))))), inference(superposition, [status(thm), theory('equality')], [c_24852, c_18410])).
% 12.17/4.97  tff(c_25104, plain, (![A_628, A_629]: (k9_relat_1(k6_relat_1(A_628), A_629)=k3_xboole_0(A_628, A_629))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18058, c_7371, c_249, c_32, c_24879])).
% 12.17/4.97  tff(c_7158, plain, (![A_364, A_365]: (r1_tarski(k9_relat_1(k6_relat_1(A_364), A_365), A_365))), inference(resolution, [status(thm)], [c_7078, c_3481])).
% 12.17/4.97  tff(c_294, plain, (![A_48, A_93]: (k7_relat_1(k6_relat_1(A_48), A_93)=k6_relat_1(A_48) | ~r1_tarski(A_48, A_93))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_292])).
% 12.17/4.97  tff(c_25091, plain, (![A_628, A_93]: (k6_relat_1(k9_relat_1(k6_relat_1(A_628), A_93))=k7_relat_1(k6_relat_1(A_628), A_93) | ~r1_tarski(k9_relat_1(k6_relat_1(A_628), A_93), A_93))), inference(superposition, [status(thm), theory('equality')], [c_294, c_24852])).
% 12.17/4.97  tff(c_25192, plain, (![A_628, A_93]: (k6_relat_1(k9_relat_1(k6_relat_1(A_628), A_93))=k7_relat_1(k6_relat_1(A_628), A_93))), inference(demodulation, [status(thm), theory('equality')], [c_7158, c_25091])).
% 12.17/4.97  tff(c_31367, plain, (![A_628, A_93]: (k7_relat_1(k6_relat_1(A_628), A_93)=k6_relat_1(k3_xboole_0(A_628, A_93)))), inference(demodulation, [status(thm), theory('equality')], [c_25104, c_25192])).
% 12.17/4.97  tff(c_50, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.17/4.97  tff(c_161, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_50])).
% 12.17/4.97  tff(c_181, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_161])).
% 12.17/4.97  tff(c_31421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31367, c_181])).
% 12.17/4.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.17/4.97  
% 12.17/4.97  Inference rules
% 12.17/4.97  ----------------------
% 12.17/4.97  #Ref     : 0
% 12.17/4.97  #Sup     : 7576
% 12.17/4.97  #Fact    : 0
% 12.17/4.97  #Define  : 0
% 12.17/4.97  #Split   : 2
% 12.17/4.97  #Chain   : 0
% 12.17/4.97  #Close   : 0
% 12.17/4.97  
% 12.17/4.97  Ordering : KBO
% 12.17/4.97  
% 12.17/4.97  Simplification rules
% 12.17/4.97  ----------------------
% 12.17/4.97  #Subsume      : 1294
% 12.17/4.97  #Demod        : 7239
% 12.17/4.97  #Tautology    : 2802
% 12.17/4.97  #SimpNegUnit  : 0
% 12.17/4.97  #BackRed      : 109
% 12.17/4.97  
% 12.17/4.97  #Partial instantiations: 0
% 12.17/4.97  #Strategies tried      : 1
% 12.17/4.97  
% 12.17/4.97  Timing (in seconds)
% 12.17/4.97  ----------------------
% 12.17/4.97  Preprocessing        : 0.38
% 12.17/4.97  Parsing              : 0.20
% 12.17/4.97  CNF conversion       : 0.03
% 12.17/4.97  Main loop            : 3.75
% 12.17/4.97  Inferencing          : 0.88
% 12.17/4.97  Reduction            : 1.48
% 12.17/4.97  Demodulation         : 1.22
% 12.17/4.97  BG Simplification    : 0.12
% 12.17/4.97  Subsumption          : 1.04
% 12.17/4.97  Abstraction          : 0.19
% 12.17/4.97  MUC search           : 0.00
% 12.17/4.97  Cooper               : 0.00
% 12.17/4.97  Total                : 4.19
% 12.17/4.97  Index Insertion      : 0.00
% 12.17/4.97  Index Deletion       : 0.00
% 12.17/4.97  Index Matching       : 0.00
% 12.17/4.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
