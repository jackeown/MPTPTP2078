%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:33 EST 2020

% Result     : Theorem 10.61s
% Output     : CNFRefutation 10.70s
% Verified   : 
% Statistics : Number of formulae       :  155 (2943 expanded)
%              Number of leaves         :   37 (1044 expanded)
%              Depth                    :   25
%              Number of atoms          :  259 (4824 expanded)
%              Number of equality atoms :  114 (1908 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_51,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_81,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_22,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    ! [A_59,B_60] :
      ( k5_relat_1(k6_relat_1(A_59),B_60) = k7_relat_1(B_60,A_59)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    ! [A_52] : k4_relat_1(k6_relat_1(A_52)) = k6_relat_1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_682,plain,(
    ! [B_120,A_121] :
      ( k5_relat_1(k4_relat_1(B_120),k4_relat_1(A_121)) = k4_relat_1(k5_relat_1(A_121,B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_694,plain,(
    ! [A_52,A_121] :
      ( k5_relat_1(k6_relat_1(A_52),k4_relat_1(A_121)) = k4_relat_1(k5_relat_1(A_121,k6_relat_1(A_52)))
      | ~ v1_relat_1(k6_relat_1(A_52))
      | ~ v1_relat_1(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_682])).

tff(c_706,plain,(
    ! [A_122,A_123] :
      ( k5_relat_1(k6_relat_1(A_122),k4_relat_1(A_123)) = k4_relat_1(k5_relat_1(A_123,k6_relat_1(A_122)))
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_694])).

tff(c_733,plain,(
    ! [A_52,A_122] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_52),k6_relat_1(A_122))) = k5_relat_1(k6_relat_1(A_122),k6_relat_1(A_52))
      | ~ v1_relat_1(k6_relat_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_706])).

tff(c_839,plain,(
    ! [A_131,A_132] : k4_relat_1(k5_relat_1(k6_relat_1(A_131),k6_relat_1(A_132))) = k5_relat_1(k6_relat_1(A_132),k6_relat_1(A_131)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_733])).

tff(c_20,plain,(
    ! [A_34,B_35] :
      ( v1_relat_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_719,plain,(
    ! [A_123,A_122] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_123,k6_relat_1(A_122))))
      | ~ v1_relat_1(k4_relat_1(A_123))
      | ~ v1_relat_1(k6_relat_1(A_122))
      | ~ v1_relat_1(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_20])).

tff(c_736,plain,(
    ! [A_123,A_122] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(A_123,k6_relat_1(A_122))))
      | ~ v1_relat_1(k4_relat_1(A_123))
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_719])).

tff(c_845,plain,(
    ! [A_132,A_131] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_132),k6_relat_1(A_131)))
      | ~ v1_relat_1(k4_relat_1(k6_relat_1(A_131)))
      | ~ v1_relat_1(k6_relat_1(A_131)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_736])).

tff(c_888,plain,(
    ! [A_133,A_134] : v1_relat_1(k5_relat_1(k6_relat_1(A_133),k6_relat_1(A_134))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_34,c_845])).

tff(c_894,plain,(
    ! [A_134,A_59] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_134),A_59))
      | ~ v1_relat_1(k6_relat_1(A_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_888])).

tff(c_907,plain,(
    ! [A_134,A_59] : v1_relat_1(k7_relat_1(k6_relat_1(A_134),A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_894])).

tff(c_30,plain,(
    ! [A_51] : k1_relat_1(k6_relat_1(A_51)) = A_51 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [A_51] : k2_relat_1(k6_relat_1(A_51)) = A_51 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_171,plain,(
    ! [A_81,B_82] :
      ( k5_relat_1(k6_relat_1(A_81),B_82) = k7_relat_1(B_82,A_81)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    ! [A_56] :
      ( k5_relat_1(A_56,k6_relat_1(k2_relat_1(A_56))) = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_186,plain,(
    ! [A_81] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_81))),A_81) = k6_relat_1(A_81)
      | ~ v1_relat_1(k6_relat_1(A_81))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_81)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_40])).

tff(c_210,plain,(
    ! [A_81] : k7_relat_1(k6_relat_1(A_81),A_81) = k6_relat_1(A_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_32,c_186])).

tff(c_220,plain,(
    ! [B_83,A_84] :
      ( k3_xboole_0(k1_relat_1(B_83),A_84) = k1_relat_1(k7_relat_1(B_83,A_84))
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_232,plain,(
    ! [A_51,A_84] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_51),A_84)) = k3_xboole_0(A_51,A_84)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_220])).

tff(c_255,plain,(
    ! [A_88,A_89] : k1_relat_1(k7_relat_1(k6_relat_1(A_88),A_89)) = k3_xboole_0(A_88,A_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_232])).

tff(c_270,plain,(
    ! [A_81] : k3_xboole_0(A_81,A_81) = k1_relat_1(k6_relat_1(A_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_255])).

tff(c_273,plain,(
    ! [A_81] : k3_xboole_0(A_81,A_81) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_270])).

tff(c_236,plain,(
    ! [A_51,A_84] : k1_relat_1(k7_relat_1(k6_relat_1(A_51),A_84)) = k3_xboole_0(A_51,A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_232])).

tff(c_864,plain,(
    ! [A_132,A_59] :
      ( k5_relat_1(k6_relat_1(A_132),k6_relat_1(A_59)) = k4_relat_1(k7_relat_1(k6_relat_1(A_132),A_59))
      | ~ v1_relat_1(k6_relat_1(A_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_839])).

tff(c_1176,plain,(
    ! [A_151,A_152] : k5_relat_1(k6_relat_1(A_151),k6_relat_1(A_152)) = k4_relat_1(k7_relat_1(k6_relat_1(A_151),A_152)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_864])).

tff(c_1210,plain,(
    ! [A_59,A_152] :
      ( k4_relat_1(k7_relat_1(k6_relat_1(A_59),A_152)) = k7_relat_1(k6_relat_1(A_152),A_59)
      | ~ v1_relat_1(k6_relat_1(A_152)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1176])).

tff(c_1238,plain,(
    ! [A_59,A_152] : k4_relat_1(k7_relat_1(k6_relat_1(A_59),A_152)) = k7_relat_1(k6_relat_1(A_152),A_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1210])).

tff(c_882,plain,(
    ! [A_132,A_59] : k5_relat_1(k6_relat_1(A_132),k6_relat_1(A_59)) = k4_relat_1(k7_relat_1(k6_relat_1(A_132),A_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_864])).

tff(c_1342,plain,(
    ! [A_132,A_59] : k5_relat_1(k6_relat_1(A_132),k6_relat_1(A_59)) = k7_relat_1(k6_relat_1(A_59),A_132) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_882])).

tff(c_38,plain,(
    ! [A_55] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_55)),A_55) = A_55
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1244,plain,(
    ! [A_153,B_154,C_155] :
      ( k5_relat_1(k5_relat_1(A_153,B_154),C_155) = k5_relat_1(A_153,k5_relat_1(B_154,C_155))
      | ~ v1_relat_1(C_155)
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1285,plain,(
    ! [A_55,C_155] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_55)),k5_relat_1(A_55,C_155)) = k5_relat_1(A_55,C_155)
      | ~ v1_relat_1(C_155)
      | ~ v1_relat_1(A_55)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_55)))
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1244])).

tff(c_2686,plain,(
    ! [A_218,C_219] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_218)),k5_relat_1(A_218,C_219)) = k5_relat_1(A_218,C_219)
      | ~ v1_relat_1(C_219)
      | ~ v1_relat_1(A_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1285])).

tff(c_2740,plain,(
    ! [A_132,A_59] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_132))),k7_relat_1(k6_relat_1(A_59),A_132)) = k5_relat_1(k6_relat_1(A_132),k6_relat_1(A_59))
      | ~ v1_relat_1(k6_relat_1(A_59))
      | ~ v1_relat_1(k6_relat_1(A_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1342,c_2686])).

tff(c_2812,plain,(
    ! [A_220,A_221] : k5_relat_1(k6_relat_1(A_220),k7_relat_1(k6_relat_1(A_221),A_220)) = k7_relat_1(k6_relat_1(A_221),A_220) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_1342,c_30,c_2740])).

tff(c_2840,plain,(
    ! [A_221,A_220] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_221),A_220),A_220) = k7_relat_1(k6_relat_1(A_221),A_220)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_221),A_220)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2812,c_44])).

tff(c_2892,plain,(
    ! [A_222,A_223] : k7_relat_1(k7_relat_1(k6_relat_1(A_222),A_223),A_223) = k7_relat_1(k6_relat_1(A_222),A_223) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_2840])).

tff(c_42,plain,(
    ! [B_58,A_57] :
      ( k3_xboole_0(k1_relat_1(B_58),A_57) = k1_relat_1(k7_relat_1(B_58,A_57))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_353,plain,(
    ! [A_99,B_100] :
      ( k5_relat_1(k6_relat_1(A_99),B_100) = B_100
      | ~ r1_tarski(k1_relat_1(B_100),A_99)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_366,plain,(
    ! [A_99,A_51] :
      ( k5_relat_1(k6_relat_1(A_99),k6_relat_1(A_51)) = k6_relat_1(A_51)
      | ~ r1_tarski(A_51,A_99)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_353])).

tff(c_430,plain,(
    ! [A_102,A_103] :
      ( k5_relat_1(k6_relat_1(A_102),k6_relat_1(A_103)) = k6_relat_1(A_103)
      | ~ r1_tarski(A_103,A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_366])).

tff(c_436,plain,(
    ! [A_103,A_102] :
      ( k7_relat_1(k6_relat_1(A_103),A_102) = k6_relat_1(A_103)
      | ~ v1_relat_1(k6_relat_1(A_103))
      | ~ r1_tarski(A_103,A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_44])).

tff(c_497,plain,(
    ! [A_104,A_105] :
      ( k7_relat_1(k6_relat_1(A_104),A_105) = k6_relat_1(A_104)
      | ~ r1_tarski(A_104,A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_436])).

tff(c_514,plain,(
    ! [A_104,A_105] :
      ( k3_xboole_0(A_104,A_105) = k1_relat_1(k6_relat_1(A_104))
      | ~ r1_tarski(A_104,A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_236])).

tff(c_556,plain,(
    ! [A_106,A_107] :
      ( k3_xboole_0(A_106,A_107) = A_106
      | ~ r1_tarski(A_106,A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_514])).

tff(c_579,plain,(
    ! [A_113,B_114] : k3_xboole_0(k3_xboole_0(A_113,B_114),A_113) = k3_xboole_0(A_113,B_114) ),
    inference(resolution,[status(thm)],[c_2,c_556])).

tff(c_600,plain,(
    ! [B_58,A_57] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_58,A_57)),k1_relat_1(B_58)) = k3_xboole_0(k1_relat_1(B_58),A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_579])).

tff(c_2901,plain,(
    ! [A_222,A_223] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_222),A_223)),k1_relat_1(k7_relat_1(k6_relat_1(A_222),A_223))) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_222),A_223)),A_223)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_222),A_223)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2892,c_600])).

tff(c_2960,plain,(
    ! [A_222,A_223] : k3_xboole_0(k3_xboole_0(A_222,A_223),A_223) = k3_xboole_0(A_222,A_223) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_273,c_236,c_236,c_236,c_2901])).

tff(c_569,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_556])).

tff(c_198,plain,(
    ! [A_55] :
      ( k7_relat_1(A_55,k1_relat_1(A_55)) = A_55
      | ~ v1_relat_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_171])).

tff(c_740,plain,(
    ! [B_124,C_125,A_126] :
      ( k7_relat_1(k5_relat_1(B_124,C_125),A_126) = k5_relat_1(k7_relat_1(B_124,A_126),C_125)
      | ~ v1_relat_1(C_125)
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_776,plain,(
    ! [A_59,A_126,B_60] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_59),A_126),B_60) = k7_relat_1(k7_relat_1(B_60,A_59),A_126)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(k6_relat_1(A_59))
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_740])).

tff(c_793,plain,(
    ! [A_59,A_126,B_60] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_59),A_126),B_60) = k7_relat_1(k7_relat_1(B_60,A_59),A_126)
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_776])).

tff(c_15925,plain,(
    ! [A_412,A_413] :
      ( k4_relat_1(k5_relat_1(A_412,k6_relat_1(A_413))) = k7_relat_1(k4_relat_1(A_412),A_413)
      | ~ v1_relat_1(A_412)
      | ~ v1_relat_1(k4_relat_1(A_412)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_706])).

tff(c_16021,plain,(
    ! [A_59,A_126,A_413] :
      ( k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_59),A_126)),A_413) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_413),A_59),A_126))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_59),A_126))
      | ~ v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_59),A_126)))
      | ~ v1_relat_1(k6_relat_1(A_413)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_15925])).

tff(c_17467,plain,(
    ! [A_429,A_430,A_431] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_429),A_430),A_431)) = k7_relat_1(k7_relat_1(k6_relat_1(A_431),A_430),A_429) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_907,c_1238,c_907,c_1238,c_16021])).

tff(c_17575,plain,(
    ! [A_429,A_430] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_429),A_430))),A_430),A_429) = k4_relat_1(k7_relat_1(k6_relat_1(A_429),A_430))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_429),A_430))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_429),A_430)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_17467])).

tff(c_17632,plain,(
    ! [A_432,A_433] : k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_432,A_433)),A_433),A_432) = k7_relat_1(k6_relat_1(A_433),A_432) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_907,c_1238,c_236,c_17575])).

tff(c_3143,plain,(
    ! [A_228,A_229] : k3_xboole_0(k3_xboole_0(A_228,A_229),A_229) = k3_xboole_0(A_228,A_229) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_273,c_236,c_236,c_236,c_2901])).

tff(c_3208,plain,(
    ! [B_58,A_57] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_58,A_57)),A_57) = k3_xboole_0(k1_relat_1(B_58),A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3143])).

tff(c_17671,plain,(
    ! [A_432,A_433] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_432,A_433)),A_433)),A_432) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_433),A_432)),A_432)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_432,A_433)),A_433)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17632,c_3208])).

tff(c_17850,plain,(
    ! [A_433,A_432] : k3_xboole_0(A_433,A_432) = k3_xboole_0(A_432,A_433) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_2960,c_569,c_2960,c_236,c_236,c_17671])).

tff(c_370,plain,(
    ! [A_99,A_51] :
      ( k5_relat_1(k6_relat_1(A_99),k6_relat_1(A_51)) = k6_relat_1(A_51)
      | ~ r1_tarski(A_51,A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_366])).

tff(c_860,plain,(
    ! [A_51,A_99] :
      ( k5_relat_1(k6_relat_1(A_51),k6_relat_1(A_99)) = k4_relat_1(k6_relat_1(A_51))
      | ~ r1_tarski(A_51,A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_839])).

tff(c_935,plain,(
    ! [A_143,A_144] :
      ( k5_relat_1(k6_relat_1(A_143),k6_relat_1(A_144)) = k6_relat_1(A_143)
      | ~ r1_tarski(A_143,A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_860])).

tff(c_955,plain,(
    ! [A_144,A_143] :
      ( k7_relat_1(k6_relat_1(A_144),A_143) = k6_relat_1(A_143)
      | ~ v1_relat_1(k6_relat_1(A_144))
      | ~ r1_tarski(A_143,A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_44])).

tff(c_1025,plain,(
    ! [A_145,A_146] :
      ( k7_relat_1(k6_relat_1(A_145),A_146) = k6_relat_1(A_146)
      | ~ r1_tarski(A_146,A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_955])).

tff(c_1049,plain,(
    ! [A_145,A_146] :
      ( k3_xboole_0(A_145,A_146) = k1_relat_1(k6_relat_1(A_146))
      | ~ r1_tarski(A_146,A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_236])).

tff(c_1094,plain,(
    ! [A_147,A_148] :
      ( k3_xboole_0(A_147,A_148) = A_148
      | ~ r1_tarski(A_148,A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1049])).

tff(c_1112,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_1094])).

tff(c_1003,plain,(
    ! [A_144,A_143] :
      ( k7_relat_1(k6_relat_1(A_144),A_143) = k6_relat_1(A_143)
      | ~ r1_tarski(A_143,A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_955])).

tff(c_110,plain,(
    ! [A_75] :
      ( k5_relat_1(A_75,k6_relat_1(k2_relat_1(A_75))) = A_75
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_122,plain,(
    ! [A_51] :
      ( k5_relat_1(k6_relat_1(A_51),k6_relat_1(A_51)) = k6_relat_1(A_51)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_110])).

tff(c_128,plain,(
    ! [A_51] : k5_relat_1(k6_relat_1(A_51),k6_relat_1(A_51)) = k6_relat_1(A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_122])).

tff(c_782,plain,(
    ! [A_51,A_126] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_51),A_126),k6_relat_1(A_51)) = k7_relat_1(k6_relat_1(A_51),A_126)
      | ~ v1_relat_1(k6_relat_1(A_51))
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_740])).

tff(c_797,plain,(
    ! [A_51,A_126] : k5_relat_1(k7_relat_1(k6_relat_1(A_51),A_126),k6_relat_1(A_51)) = k7_relat_1(k6_relat_1(A_51),A_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_782])).

tff(c_2734,plain,(
    ! [A_51,A_126] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_51),A_126))),k7_relat_1(k6_relat_1(A_51),A_126)) = k5_relat_1(k7_relat_1(k6_relat_1(A_51),A_126),k6_relat_1(A_51))
      | ~ v1_relat_1(k6_relat_1(A_51))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_51),A_126)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_2686])).

tff(c_5247,plain,(
    ! [A_267,A_268] : k5_relat_1(k6_relat_1(k3_xboole_0(A_267,A_268)),k7_relat_1(k6_relat_1(A_267),A_268)) = k7_relat_1(k6_relat_1(A_267),A_268) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_22,c_797,c_236,c_2734])).

tff(c_5314,plain,(
    ! [A_144,A_143] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(A_144,A_143)),k6_relat_1(A_143)) = k7_relat_1(k6_relat_1(A_144),A_143)
      | ~ r1_tarski(A_143,A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1003,c_5247])).

tff(c_6256,plain,(
    ! [A_281,A_282] :
      ( k7_relat_1(k6_relat_1(A_281),k3_xboole_0(A_282,A_281)) = k7_relat_1(k6_relat_1(A_282),A_281)
      | ~ r1_tarski(A_281,A_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1342,c_5314])).

tff(c_6375,plain,(
    ! [A_1,B_2] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(A_1,B_2)),k3_xboole_0(A_1,B_2)) = k7_relat_1(k6_relat_1(A_1),k3_xboole_0(A_1,B_2))
      | ~ r1_tarski(k3_xboole_0(A_1,B_2),A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_6256])).

tff(c_6441,plain,(
    ! [A_1,B_2] : k7_relat_1(k6_relat_1(A_1),k3_xboole_0(A_1,B_2)) = k6_relat_1(k3_xboole_0(A_1,B_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_210,c_6375])).

tff(c_475,plain,(
    ! [A_103,A_102] :
      ( k7_relat_1(k6_relat_1(A_103),A_102) = k6_relat_1(A_103)
      | ~ r1_tarski(A_103,A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_436])).

tff(c_5326,plain,(
    ! [A_103,A_102] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(A_103,A_102)),k6_relat_1(A_103)) = k7_relat_1(k6_relat_1(A_103),A_102)
      | ~ r1_tarski(A_103,A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_5247])).

tff(c_5374,plain,(
    ! [A_103,A_102] :
      ( k7_relat_1(k6_relat_1(A_103),k3_xboole_0(A_103,A_102)) = k7_relat_1(k6_relat_1(A_103),A_102)
      | ~ r1_tarski(A_103,A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1342,c_5326])).

tff(c_7678,plain,(
    ! [A_297,A_298] :
      ( k7_relat_1(k6_relat_1(A_297),A_298) = k6_relat_1(k3_xboole_0(A_297,A_298))
      | ~ r1_tarski(A_297,A_298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6441,c_5374])).

tff(c_7808,plain,(
    ! [A_297,A_298] :
      ( k4_relat_1(k6_relat_1(k3_xboole_0(A_297,A_298))) = k7_relat_1(k6_relat_1(A_298),A_297)
      | ~ r1_tarski(A_297,A_298) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7678,c_1238])).

tff(c_7957,plain,(
    ! [A_299,A_300] :
      ( k7_relat_1(k6_relat_1(A_299),A_300) = k6_relat_1(k3_xboole_0(A_300,A_299))
      | ~ r1_tarski(A_300,A_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7808])).

tff(c_226,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_83,A_84)),k1_relat_1(B_83))
      | ~ v1_relat_1(B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_2])).

tff(c_8105,plain,(
    ! [A_300,A_299] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_300,A_299))),k1_relat_1(k6_relat_1(A_299)))
      | ~ v1_relat_1(k6_relat_1(A_299))
      | ~ r1_tarski(A_300,A_299) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7957,c_226])).

tff(c_8459,plain,(
    ! [A_303,A_304] :
      ( r1_tarski(k3_xboole_0(A_303,A_304),A_304)
      | ~ r1_tarski(A_303,A_304) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_30,c_30,c_8105])).

tff(c_8512,plain,(
    ! [B_58,A_57] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_58,A_57)),A_57)
      | ~ r1_tarski(k1_relat_1(B_58),A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_8459])).

tff(c_17650,plain,(
    ! [A_433,A_432] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_433),A_432)),A_432)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_432,A_433)),A_433)),A_432)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_432,A_433)),A_433)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17632,c_8512])).

tff(c_17836,plain,(
    ! [A_433,A_432] : r1_tarski(k3_xboole_0(A_433,A_432),A_432) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_2,c_2960,c_236,c_236,c_17650])).

tff(c_6743,plain,(
    ! [A_286,B_287] : k7_relat_1(k6_relat_1(A_286),k3_xboole_0(A_286,B_287)) = k6_relat_1(k3_xboole_0(A_286,B_287)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_210,c_6375])).

tff(c_6825,plain,(
    ! [A_286,B_287] : k7_relat_1(k6_relat_1(k3_xboole_0(A_286,B_287)),A_286) = k4_relat_1(k6_relat_1(k3_xboole_0(A_286,B_287))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6743,c_1238])).

tff(c_6938,plain,(
    ! [A_286,B_287] : k7_relat_1(k6_relat_1(k3_xboole_0(A_286,B_287)),A_286) = k6_relat_1(k3_xboole_0(A_286,B_287)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6825])).

tff(c_17630,plain,(
    ! [A_429,A_430] : k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_429,A_430)),A_430),A_429) = k7_relat_1(k6_relat_1(A_430),A_429) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_907,c_1238,c_236,c_17575])).

tff(c_1398,plain,(
    ! [A_167,A_168] : k5_relat_1(k6_relat_1(A_167),k6_relat_1(A_168)) = k7_relat_1(k6_relat_1(A_168),A_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_882])).

tff(c_24,plain,(
    ! [B_38,C_40,A_37] :
      ( k7_relat_1(k5_relat_1(B_38,C_40),A_37) = k5_relat_1(k7_relat_1(B_38,A_37),C_40)
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1410,plain,(
    ! [A_167,A_37,A_168] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_167),A_37),k6_relat_1(A_168)) = k7_relat_1(k7_relat_1(k6_relat_1(A_168),A_167),A_37)
      | ~ v1_relat_1(k6_relat_1(A_168))
      | ~ v1_relat_1(k6_relat_1(A_167)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1398,c_24])).

tff(c_1453,plain,(
    ! [A_167,A_37,A_168] : k5_relat_1(k7_relat_1(k6_relat_1(A_167),A_37),k6_relat_1(A_168)) = k7_relat_1(k7_relat_1(k6_relat_1(A_168),A_167),A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_1410])).

tff(c_769,plain,(
    ! [A_99,A_126,A_51] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_99),A_126),k6_relat_1(A_51)) = k7_relat_1(k6_relat_1(A_51),A_126)
      | ~ v1_relat_1(k6_relat_1(A_51))
      | ~ v1_relat_1(k6_relat_1(A_99))
      | ~ r1_tarski(A_51,A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_740])).

tff(c_791,plain,(
    ! [A_99,A_126,A_51] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_99),A_126),k6_relat_1(A_51)) = k7_relat_1(k6_relat_1(A_51),A_126)
      | ~ r1_tarski(A_51,A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_769])).

tff(c_20422,plain,(
    ! [A_463,A_464,A_465] :
      ( k7_relat_1(k7_relat_1(k6_relat_1(A_463),A_464),A_465) = k7_relat_1(k6_relat_1(A_463),A_465)
      | ~ r1_tarski(A_463,A_464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_791])).

tff(c_20546,plain,(
    ! [A_429,A_430] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(A_429,A_430)),A_429) = k7_relat_1(k6_relat_1(A_430),A_429)
      | ~ r1_tarski(k3_xboole_0(A_429,A_430),A_430) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17630,c_20422])).

tff(c_20683,plain,(
    ! [A_430,A_429] : k7_relat_1(k6_relat_1(A_430),A_429) = k6_relat_1(k3_xboole_0(A_429,A_430)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17836,c_6938,c_20546])).

tff(c_46,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_189,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_46])).

tff(c_212,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_189])).

tff(c_24692,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20683,c_212])).

tff(c_24702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17850,c_24692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.61/4.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.61/4.06  
% 10.61/4.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.70/4.06  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 10.70/4.06  
% 10.70/4.06  %Foreground sorts:
% 10.70/4.06  
% 10.70/4.06  
% 10.70/4.06  %Background operators:
% 10.70/4.06  
% 10.70/4.06  
% 10.70/4.06  %Foreground operators:
% 10.70/4.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.70/4.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.70/4.06  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.70/4.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.70/4.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.70/4.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.70/4.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.70/4.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.70/4.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.70/4.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.70/4.06  tff('#skF_2', type, '#skF_2': $i).
% 10.70/4.06  tff('#skF_1', type, '#skF_1': $i).
% 10.70/4.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.70/4.06  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.70/4.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.70/4.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.70/4.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.70/4.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.70/4.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.70/4.06  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.70/4.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.70/4.06  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 10.70/4.06  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.70/4.06  
% 10.70/4.09  tff(f_51, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 10.70/4.09  tff(f_103, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 10.70/4.09  tff(f_81, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 10.70/4.09  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 10.70/4.09  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 10.70/4.09  tff(f_79, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 10.70/4.09  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 10.70/4.09  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 10.70/4.09  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 10.70/4.09  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 10.70/4.09  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.70/4.09  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 10.70/4.09  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 10.70/4.09  tff(f_106, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 10.70/4.09  tff(c_22, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.70/4.09  tff(c_44, plain, (![A_59, B_60]: (k5_relat_1(k6_relat_1(A_59), B_60)=k7_relat_1(B_60, A_59) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.70/4.09  tff(c_34, plain, (![A_52]: (k4_relat_1(k6_relat_1(A_52))=k6_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.70/4.09  tff(c_682, plain, (![B_120, A_121]: (k5_relat_1(k4_relat_1(B_120), k4_relat_1(A_121))=k4_relat_1(k5_relat_1(A_121, B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.70/4.09  tff(c_694, plain, (![A_52, A_121]: (k5_relat_1(k6_relat_1(A_52), k4_relat_1(A_121))=k4_relat_1(k5_relat_1(A_121, k6_relat_1(A_52))) | ~v1_relat_1(k6_relat_1(A_52)) | ~v1_relat_1(A_121))), inference(superposition, [status(thm), theory('equality')], [c_34, c_682])).
% 10.70/4.09  tff(c_706, plain, (![A_122, A_123]: (k5_relat_1(k6_relat_1(A_122), k4_relat_1(A_123))=k4_relat_1(k5_relat_1(A_123, k6_relat_1(A_122))) | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_694])).
% 10.70/4.09  tff(c_733, plain, (![A_52, A_122]: (k4_relat_1(k5_relat_1(k6_relat_1(A_52), k6_relat_1(A_122)))=k5_relat_1(k6_relat_1(A_122), k6_relat_1(A_52)) | ~v1_relat_1(k6_relat_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_706])).
% 10.70/4.09  tff(c_839, plain, (![A_131, A_132]: (k4_relat_1(k5_relat_1(k6_relat_1(A_131), k6_relat_1(A_132)))=k5_relat_1(k6_relat_1(A_132), k6_relat_1(A_131)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_733])).
% 10.70/4.09  tff(c_20, plain, (![A_34, B_35]: (v1_relat_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.70/4.09  tff(c_719, plain, (![A_123, A_122]: (v1_relat_1(k4_relat_1(k5_relat_1(A_123, k6_relat_1(A_122)))) | ~v1_relat_1(k4_relat_1(A_123)) | ~v1_relat_1(k6_relat_1(A_122)) | ~v1_relat_1(A_123))), inference(superposition, [status(thm), theory('equality')], [c_706, c_20])).
% 10.70/4.09  tff(c_736, plain, (![A_123, A_122]: (v1_relat_1(k4_relat_1(k5_relat_1(A_123, k6_relat_1(A_122)))) | ~v1_relat_1(k4_relat_1(A_123)) | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_719])).
% 10.70/4.09  tff(c_845, plain, (![A_132, A_131]: (v1_relat_1(k5_relat_1(k6_relat_1(A_132), k6_relat_1(A_131))) | ~v1_relat_1(k4_relat_1(k6_relat_1(A_131))) | ~v1_relat_1(k6_relat_1(A_131)))), inference(superposition, [status(thm), theory('equality')], [c_839, c_736])).
% 10.70/4.09  tff(c_888, plain, (![A_133, A_134]: (v1_relat_1(k5_relat_1(k6_relat_1(A_133), k6_relat_1(A_134))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_34, c_845])).
% 10.70/4.09  tff(c_894, plain, (![A_134, A_59]: (v1_relat_1(k7_relat_1(k6_relat_1(A_134), A_59)) | ~v1_relat_1(k6_relat_1(A_134)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_888])).
% 10.70/4.09  tff(c_907, plain, (![A_134, A_59]: (v1_relat_1(k7_relat_1(k6_relat_1(A_134), A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_894])).
% 10.70/4.09  tff(c_30, plain, (![A_51]: (k1_relat_1(k6_relat_1(A_51))=A_51)), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.70/4.09  tff(c_32, plain, (![A_51]: (k2_relat_1(k6_relat_1(A_51))=A_51)), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.70/4.09  tff(c_171, plain, (![A_81, B_82]: (k5_relat_1(k6_relat_1(A_81), B_82)=k7_relat_1(B_82, A_81) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.70/4.09  tff(c_40, plain, (![A_56]: (k5_relat_1(A_56, k6_relat_1(k2_relat_1(A_56)))=A_56 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.70/4.09  tff(c_186, plain, (![A_81]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_81))), A_81)=k6_relat_1(A_81) | ~v1_relat_1(k6_relat_1(A_81)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_81)))))), inference(superposition, [status(thm), theory('equality')], [c_171, c_40])).
% 10.70/4.09  tff(c_210, plain, (![A_81]: (k7_relat_1(k6_relat_1(A_81), A_81)=k6_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_32, c_186])).
% 10.70/4.09  tff(c_220, plain, (![B_83, A_84]: (k3_xboole_0(k1_relat_1(B_83), A_84)=k1_relat_1(k7_relat_1(B_83, A_84)) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.70/4.09  tff(c_232, plain, (![A_51, A_84]: (k1_relat_1(k7_relat_1(k6_relat_1(A_51), A_84))=k3_xboole_0(A_51, A_84) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_220])).
% 10.70/4.09  tff(c_255, plain, (![A_88, A_89]: (k1_relat_1(k7_relat_1(k6_relat_1(A_88), A_89))=k3_xboole_0(A_88, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_232])).
% 10.70/4.09  tff(c_270, plain, (![A_81]: (k3_xboole_0(A_81, A_81)=k1_relat_1(k6_relat_1(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_210, c_255])).
% 10.70/4.09  tff(c_273, plain, (![A_81]: (k3_xboole_0(A_81, A_81)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_270])).
% 10.70/4.09  tff(c_236, plain, (![A_51, A_84]: (k1_relat_1(k7_relat_1(k6_relat_1(A_51), A_84))=k3_xboole_0(A_51, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_232])).
% 10.70/4.09  tff(c_864, plain, (![A_132, A_59]: (k5_relat_1(k6_relat_1(A_132), k6_relat_1(A_59))=k4_relat_1(k7_relat_1(k6_relat_1(A_132), A_59)) | ~v1_relat_1(k6_relat_1(A_132)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_839])).
% 10.70/4.09  tff(c_1176, plain, (![A_151, A_152]: (k5_relat_1(k6_relat_1(A_151), k6_relat_1(A_152))=k4_relat_1(k7_relat_1(k6_relat_1(A_151), A_152)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_864])).
% 10.70/4.09  tff(c_1210, plain, (![A_59, A_152]: (k4_relat_1(k7_relat_1(k6_relat_1(A_59), A_152))=k7_relat_1(k6_relat_1(A_152), A_59) | ~v1_relat_1(k6_relat_1(A_152)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1176])).
% 10.70/4.09  tff(c_1238, plain, (![A_59, A_152]: (k4_relat_1(k7_relat_1(k6_relat_1(A_59), A_152))=k7_relat_1(k6_relat_1(A_152), A_59))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1210])).
% 10.70/4.09  tff(c_882, plain, (![A_132, A_59]: (k5_relat_1(k6_relat_1(A_132), k6_relat_1(A_59))=k4_relat_1(k7_relat_1(k6_relat_1(A_132), A_59)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_864])).
% 10.70/4.09  tff(c_1342, plain, (![A_132, A_59]: (k5_relat_1(k6_relat_1(A_132), k6_relat_1(A_59))=k7_relat_1(k6_relat_1(A_59), A_132))), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_882])).
% 10.70/4.09  tff(c_38, plain, (![A_55]: (k5_relat_1(k6_relat_1(k1_relat_1(A_55)), A_55)=A_55 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.70/4.09  tff(c_1244, plain, (![A_153, B_154, C_155]: (k5_relat_1(k5_relat_1(A_153, B_154), C_155)=k5_relat_1(A_153, k5_relat_1(B_154, C_155)) | ~v1_relat_1(C_155) | ~v1_relat_1(B_154) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.70/4.09  tff(c_1285, plain, (![A_55, C_155]: (k5_relat_1(k6_relat_1(k1_relat_1(A_55)), k5_relat_1(A_55, C_155))=k5_relat_1(A_55, C_155) | ~v1_relat_1(C_155) | ~v1_relat_1(A_55) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_55))) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1244])).
% 10.70/4.09  tff(c_2686, plain, (![A_218, C_219]: (k5_relat_1(k6_relat_1(k1_relat_1(A_218)), k5_relat_1(A_218, C_219))=k5_relat_1(A_218, C_219) | ~v1_relat_1(C_219) | ~v1_relat_1(A_218))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1285])).
% 10.70/4.09  tff(c_2740, plain, (![A_132, A_59]: (k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_132))), k7_relat_1(k6_relat_1(A_59), A_132))=k5_relat_1(k6_relat_1(A_132), k6_relat_1(A_59)) | ~v1_relat_1(k6_relat_1(A_59)) | ~v1_relat_1(k6_relat_1(A_132)))), inference(superposition, [status(thm), theory('equality')], [c_1342, c_2686])).
% 10.70/4.09  tff(c_2812, plain, (![A_220, A_221]: (k5_relat_1(k6_relat_1(A_220), k7_relat_1(k6_relat_1(A_221), A_220))=k7_relat_1(k6_relat_1(A_221), A_220))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_1342, c_30, c_2740])).
% 10.70/4.09  tff(c_2840, plain, (![A_221, A_220]: (k7_relat_1(k7_relat_1(k6_relat_1(A_221), A_220), A_220)=k7_relat_1(k6_relat_1(A_221), A_220) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_221), A_220)))), inference(superposition, [status(thm), theory('equality')], [c_2812, c_44])).
% 10.70/4.09  tff(c_2892, plain, (![A_222, A_223]: (k7_relat_1(k7_relat_1(k6_relat_1(A_222), A_223), A_223)=k7_relat_1(k6_relat_1(A_222), A_223))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_2840])).
% 10.70/4.09  tff(c_42, plain, (![B_58, A_57]: (k3_xboole_0(k1_relat_1(B_58), A_57)=k1_relat_1(k7_relat_1(B_58, A_57)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.70/4.09  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.70/4.09  tff(c_353, plain, (![A_99, B_100]: (k5_relat_1(k6_relat_1(A_99), B_100)=B_100 | ~r1_tarski(k1_relat_1(B_100), A_99) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.70/4.09  tff(c_366, plain, (![A_99, A_51]: (k5_relat_1(k6_relat_1(A_99), k6_relat_1(A_51))=k6_relat_1(A_51) | ~r1_tarski(A_51, A_99) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_353])).
% 10.70/4.09  tff(c_430, plain, (![A_102, A_103]: (k5_relat_1(k6_relat_1(A_102), k6_relat_1(A_103))=k6_relat_1(A_103) | ~r1_tarski(A_103, A_102))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_366])).
% 10.70/4.09  tff(c_436, plain, (![A_103, A_102]: (k7_relat_1(k6_relat_1(A_103), A_102)=k6_relat_1(A_103) | ~v1_relat_1(k6_relat_1(A_103)) | ~r1_tarski(A_103, A_102))), inference(superposition, [status(thm), theory('equality')], [c_430, c_44])).
% 10.70/4.09  tff(c_497, plain, (![A_104, A_105]: (k7_relat_1(k6_relat_1(A_104), A_105)=k6_relat_1(A_104) | ~r1_tarski(A_104, A_105))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_436])).
% 10.70/4.09  tff(c_514, plain, (![A_104, A_105]: (k3_xboole_0(A_104, A_105)=k1_relat_1(k6_relat_1(A_104)) | ~r1_tarski(A_104, A_105))), inference(superposition, [status(thm), theory('equality')], [c_497, c_236])).
% 10.70/4.09  tff(c_556, plain, (![A_106, A_107]: (k3_xboole_0(A_106, A_107)=A_106 | ~r1_tarski(A_106, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_514])).
% 10.70/4.09  tff(c_579, plain, (![A_113, B_114]: (k3_xboole_0(k3_xboole_0(A_113, B_114), A_113)=k3_xboole_0(A_113, B_114))), inference(resolution, [status(thm)], [c_2, c_556])).
% 10.70/4.09  tff(c_600, plain, (![B_58, A_57]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_58, A_57)), k1_relat_1(B_58))=k3_xboole_0(k1_relat_1(B_58), A_57) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_42, c_579])).
% 10.70/4.09  tff(c_2901, plain, (![A_222, A_223]: (k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_222), A_223)), k1_relat_1(k7_relat_1(k6_relat_1(A_222), A_223)))=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_222), A_223)), A_223) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_222), A_223)))), inference(superposition, [status(thm), theory('equality')], [c_2892, c_600])).
% 10.70/4.09  tff(c_2960, plain, (![A_222, A_223]: (k3_xboole_0(k3_xboole_0(A_222, A_223), A_223)=k3_xboole_0(A_222, A_223))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_273, c_236, c_236, c_236, c_2901])).
% 10.70/4.09  tff(c_569, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_556])).
% 10.70/4.09  tff(c_198, plain, (![A_55]: (k7_relat_1(A_55, k1_relat_1(A_55))=A_55 | ~v1_relat_1(A_55) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_38, c_171])).
% 10.70/4.09  tff(c_740, plain, (![B_124, C_125, A_126]: (k7_relat_1(k5_relat_1(B_124, C_125), A_126)=k5_relat_1(k7_relat_1(B_124, A_126), C_125) | ~v1_relat_1(C_125) | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.70/4.09  tff(c_776, plain, (![A_59, A_126, B_60]: (k5_relat_1(k7_relat_1(k6_relat_1(A_59), A_126), B_60)=k7_relat_1(k7_relat_1(B_60, A_59), A_126) | ~v1_relat_1(B_60) | ~v1_relat_1(k6_relat_1(A_59)) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_44, c_740])).
% 10.70/4.09  tff(c_793, plain, (![A_59, A_126, B_60]: (k5_relat_1(k7_relat_1(k6_relat_1(A_59), A_126), B_60)=k7_relat_1(k7_relat_1(B_60, A_59), A_126) | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_776])).
% 10.70/4.09  tff(c_15925, plain, (![A_412, A_413]: (k4_relat_1(k5_relat_1(A_412, k6_relat_1(A_413)))=k7_relat_1(k4_relat_1(A_412), A_413) | ~v1_relat_1(A_412) | ~v1_relat_1(k4_relat_1(A_412)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_706])).
% 10.70/4.09  tff(c_16021, plain, (![A_59, A_126, A_413]: (k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_59), A_126)), A_413)=k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_413), A_59), A_126)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_59), A_126)) | ~v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(A_59), A_126))) | ~v1_relat_1(k6_relat_1(A_413)))), inference(superposition, [status(thm), theory('equality')], [c_793, c_15925])).
% 10.70/4.09  tff(c_17467, plain, (![A_429, A_430, A_431]: (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(A_429), A_430), A_431))=k7_relat_1(k7_relat_1(k6_relat_1(A_431), A_430), A_429))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_907, c_1238, c_907, c_1238, c_16021])).
% 10.70/4.09  tff(c_17575, plain, (![A_429, A_430]: (k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_429), A_430))), A_430), A_429)=k4_relat_1(k7_relat_1(k6_relat_1(A_429), A_430)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_429), A_430)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_429), A_430)))), inference(superposition, [status(thm), theory('equality')], [c_198, c_17467])).
% 10.70/4.09  tff(c_17632, plain, (![A_432, A_433]: (k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_432, A_433)), A_433), A_432)=k7_relat_1(k6_relat_1(A_433), A_432))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_907, c_1238, c_236, c_17575])).
% 10.70/4.09  tff(c_3143, plain, (![A_228, A_229]: (k3_xboole_0(k3_xboole_0(A_228, A_229), A_229)=k3_xboole_0(A_228, A_229))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_273, c_236, c_236, c_236, c_2901])).
% 10.70/4.09  tff(c_3208, plain, (![B_58, A_57]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_58, A_57)), A_57)=k3_xboole_0(k1_relat_1(B_58), A_57) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_42, c_3143])).
% 10.70/4.09  tff(c_17671, plain, (![A_432, A_433]: (k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_432, A_433)), A_433)), A_432)=k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(A_433), A_432)), A_432) | ~v1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_432, A_433)), A_433)))), inference(superposition, [status(thm), theory('equality')], [c_17632, c_3208])).
% 10.70/4.09  tff(c_17850, plain, (![A_433, A_432]: (k3_xboole_0(A_433, A_432)=k3_xboole_0(A_432, A_433))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_2960, c_569, c_2960, c_236, c_236, c_17671])).
% 10.70/4.09  tff(c_370, plain, (![A_99, A_51]: (k5_relat_1(k6_relat_1(A_99), k6_relat_1(A_51))=k6_relat_1(A_51) | ~r1_tarski(A_51, A_99))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_366])).
% 10.70/4.09  tff(c_860, plain, (![A_51, A_99]: (k5_relat_1(k6_relat_1(A_51), k6_relat_1(A_99))=k4_relat_1(k6_relat_1(A_51)) | ~r1_tarski(A_51, A_99))), inference(superposition, [status(thm), theory('equality')], [c_370, c_839])).
% 10.70/4.09  tff(c_935, plain, (![A_143, A_144]: (k5_relat_1(k6_relat_1(A_143), k6_relat_1(A_144))=k6_relat_1(A_143) | ~r1_tarski(A_143, A_144))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_860])).
% 10.70/4.09  tff(c_955, plain, (![A_144, A_143]: (k7_relat_1(k6_relat_1(A_144), A_143)=k6_relat_1(A_143) | ~v1_relat_1(k6_relat_1(A_144)) | ~r1_tarski(A_143, A_144))), inference(superposition, [status(thm), theory('equality')], [c_935, c_44])).
% 10.70/4.09  tff(c_1025, plain, (![A_145, A_146]: (k7_relat_1(k6_relat_1(A_145), A_146)=k6_relat_1(A_146) | ~r1_tarski(A_146, A_145))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_955])).
% 10.70/4.09  tff(c_1049, plain, (![A_145, A_146]: (k3_xboole_0(A_145, A_146)=k1_relat_1(k6_relat_1(A_146)) | ~r1_tarski(A_146, A_145))), inference(superposition, [status(thm), theory('equality')], [c_1025, c_236])).
% 10.70/4.09  tff(c_1094, plain, (![A_147, A_148]: (k3_xboole_0(A_147, A_148)=A_148 | ~r1_tarski(A_148, A_147))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1049])).
% 10.70/4.09  tff(c_1112, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_1094])).
% 10.70/4.09  tff(c_1003, plain, (![A_144, A_143]: (k7_relat_1(k6_relat_1(A_144), A_143)=k6_relat_1(A_143) | ~r1_tarski(A_143, A_144))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_955])).
% 10.70/4.09  tff(c_110, plain, (![A_75]: (k5_relat_1(A_75, k6_relat_1(k2_relat_1(A_75)))=A_75 | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.70/4.09  tff(c_122, plain, (![A_51]: (k5_relat_1(k6_relat_1(A_51), k6_relat_1(A_51))=k6_relat_1(A_51) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_110])).
% 10.70/4.09  tff(c_128, plain, (![A_51]: (k5_relat_1(k6_relat_1(A_51), k6_relat_1(A_51))=k6_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_122])).
% 10.70/4.09  tff(c_782, plain, (![A_51, A_126]: (k5_relat_1(k7_relat_1(k6_relat_1(A_51), A_126), k6_relat_1(A_51))=k7_relat_1(k6_relat_1(A_51), A_126) | ~v1_relat_1(k6_relat_1(A_51)) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_740])).
% 10.70/4.09  tff(c_797, plain, (![A_51, A_126]: (k5_relat_1(k7_relat_1(k6_relat_1(A_51), A_126), k6_relat_1(A_51))=k7_relat_1(k6_relat_1(A_51), A_126))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_782])).
% 10.70/4.09  tff(c_2734, plain, (![A_51, A_126]: (k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(A_51), A_126))), k7_relat_1(k6_relat_1(A_51), A_126))=k5_relat_1(k7_relat_1(k6_relat_1(A_51), A_126), k6_relat_1(A_51)) | ~v1_relat_1(k6_relat_1(A_51)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_51), A_126)))), inference(superposition, [status(thm), theory('equality')], [c_797, c_2686])).
% 10.70/4.09  tff(c_5247, plain, (![A_267, A_268]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_267, A_268)), k7_relat_1(k6_relat_1(A_267), A_268))=k7_relat_1(k6_relat_1(A_267), A_268))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_22, c_797, c_236, c_2734])).
% 10.70/4.09  tff(c_5314, plain, (![A_144, A_143]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_144, A_143)), k6_relat_1(A_143))=k7_relat_1(k6_relat_1(A_144), A_143) | ~r1_tarski(A_143, A_144))), inference(superposition, [status(thm), theory('equality')], [c_1003, c_5247])).
% 10.70/4.09  tff(c_6256, plain, (![A_281, A_282]: (k7_relat_1(k6_relat_1(A_281), k3_xboole_0(A_282, A_281))=k7_relat_1(k6_relat_1(A_282), A_281) | ~r1_tarski(A_281, A_282))), inference(demodulation, [status(thm), theory('equality')], [c_1342, c_5314])).
% 10.70/4.09  tff(c_6375, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_1, B_2)), k3_xboole_0(A_1, B_2))=k7_relat_1(k6_relat_1(A_1), k3_xboole_0(A_1, B_2)) | ~r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_1112, c_6256])).
% 10.70/4.09  tff(c_6441, plain, (![A_1, B_2]: (k7_relat_1(k6_relat_1(A_1), k3_xboole_0(A_1, B_2))=k6_relat_1(k3_xboole_0(A_1, B_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_210, c_6375])).
% 10.70/4.09  tff(c_475, plain, (![A_103, A_102]: (k7_relat_1(k6_relat_1(A_103), A_102)=k6_relat_1(A_103) | ~r1_tarski(A_103, A_102))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_436])).
% 10.70/4.09  tff(c_5326, plain, (![A_103, A_102]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_103, A_102)), k6_relat_1(A_103))=k7_relat_1(k6_relat_1(A_103), A_102) | ~r1_tarski(A_103, A_102))), inference(superposition, [status(thm), theory('equality')], [c_475, c_5247])).
% 10.70/4.09  tff(c_5374, plain, (![A_103, A_102]: (k7_relat_1(k6_relat_1(A_103), k3_xboole_0(A_103, A_102))=k7_relat_1(k6_relat_1(A_103), A_102) | ~r1_tarski(A_103, A_102))), inference(demodulation, [status(thm), theory('equality')], [c_1342, c_5326])).
% 10.70/4.09  tff(c_7678, plain, (![A_297, A_298]: (k7_relat_1(k6_relat_1(A_297), A_298)=k6_relat_1(k3_xboole_0(A_297, A_298)) | ~r1_tarski(A_297, A_298))), inference(demodulation, [status(thm), theory('equality')], [c_6441, c_5374])).
% 10.70/4.09  tff(c_7808, plain, (![A_297, A_298]: (k4_relat_1(k6_relat_1(k3_xboole_0(A_297, A_298)))=k7_relat_1(k6_relat_1(A_298), A_297) | ~r1_tarski(A_297, A_298))), inference(superposition, [status(thm), theory('equality')], [c_7678, c_1238])).
% 10.70/4.09  tff(c_7957, plain, (![A_299, A_300]: (k7_relat_1(k6_relat_1(A_299), A_300)=k6_relat_1(k3_xboole_0(A_300, A_299)) | ~r1_tarski(A_300, A_299))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7808])).
% 10.70/4.09  tff(c_226, plain, (![B_83, A_84]: (r1_tarski(k1_relat_1(k7_relat_1(B_83, A_84)), k1_relat_1(B_83)) | ~v1_relat_1(B_83))), inference(superposition, [status(thm), theory('equality')], [c_220, c_2])).
% 10.70/4.09  tff(c_8105, plain, (![A_300, A_299]: (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_300, A_299))), k1_relat_1(k6_relat_1(A_299))) | ~v1_relat_1(k6_relat_1(A_299)) | ~r1_tarski(A_300, A_299))), inference(superposition, [status(thm), theory('equality')], [c_7957, c_226])).
% 10.70/4.09  tff(c_8459, plain, (![A_303, A_304]: (r1_tarski(k3_xboole_0(A_303, A_304), A_304) | ~r1_tarski(A_303, A_304))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_30, c_30, c_8105])).
% 10.70/4.09  tff(c_8512, plain, (![B_58, A_57]: (r1_tarski(k1_relat_1(k7_relat_1(B_58, A_57)), A_57) | ~r1_tarski(k1_relat_1(B_58), A_57) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_42, c_8459])).
% 10.70/4.09  tff(c_17650, plain, (![A_433, A_432]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_433), A_432)), A_432) | ~r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_432, A_433)), A_433)), A_432) | ~v1_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_432, A_433)), A_433)))), inference(superposition, [status(thm), theory('equality')], [c_17632, c_8512])).
% 10.70/4.09  tff(c_17836, plain, (![A_433, A_432]: (r1_tarski(k3_xboole_0(A_433, A_432), A_432))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_2, c_2960, c_236, c_236, c_17650])).
% 10.70/4.09  tff(c_6743, plain, (![A_286, B_287]: (k7_relat_1(k6_relat_1(A_286), k3_xboole_0(A_286, B_287))=k6_relat_1(k3_xboole_0(A_286, B_287)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_210, c_6375])).
% 10.70/4.09  tff(c_6825, plain, (![A_286, B_287]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_286, B_287)), A_286)=k4_relat_1(k6_relat_1(k3_xboole_0(A_286, B_287))))), inference(superposition, [status(thm), theory('equality')], [c_6743, c_1238])).
% 10.70/4.09  tff(c_6938, plain, (![A_286, B_287]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_286, B_287)), A_286)=k6_relat_1(k3_xboole_0(A_286, B_287)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6825])).
% 10.70/4.09  tff(c_17630, plain, (![A_429, A_430]: (k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(A_429, A_430)), A_430), A_429)=k7_relat_1(k6_relat_1(A_430), A_429))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_907, c_1238, c_236, c_17575])).
% 10.70/4.09  tff(c_1398, plain, (![A_167, A_168]: (k5_relat_1(k6_relat_1(A_167), k6_relat_1(A_168))=k7_relat_1(k6_relat_1(A_168), A_167))), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_882])).
% 10.70/4.09  tff(c_24, plain, (![B_38, C_40, A_37]: (k7_relat_1(k5_relat_1(B_38, C_40), A_37)=k5_relat_1(k7_relat_1(B_38, A_37), C_40) | ~v1_relat_1(C_40) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.70/4.09  tff(c_1410, plain, (![A_167, A_37, A_168]: (k5_relat_1(k7_relat_1(k6_relat_1(A_167), A_37), k6_relat_1(A_168))=k7_relat_1(k7_relat_1(k6_relat_1(A_168), A_167), A_37) | ~v1_relat_1(k6_relat_1(A_168)) | ~v1_relat_1(k6_relat_1(A_167)))), inference(superposition, [status(thm), theory('equality')], [c_1398, c_24])).
% 10.70/4.09  tff(c_1453, plain, (![A_167, A_37, A_168]: (k5_relat_1(k7_relat_1(k6_relat_1(A_167), A_37), k6_relat_1(A_168))=k7_relat_1(k7_relat_1(k6_relat_1(A_168), A_167), A_37))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_1410])).
% 10.70/4.09  tff(c_769, plain, (![A_99, A_126, A_51]: (k5_relat_1(k7_relat_1(k6_relat_1(A_99), A_126), k6_relat_1(A_51))=k7_relat_1(k6_relat_1(A_51), A_126) | ~v1_relat_1(k6_relat_1(A_51)) | ~v1_relat_1(k6_relat_1(A_99)) | ~r1_tarski(A_51, A_99))), inference(superposition, [status(thm), theory('equality')], [c_370, c_740])).
% 10.70/4.09  tff(c_791, plain, (![A_99, A_126, A_51]: (k5_relat_1(k7_relat_1(k6_relat_1(A_99), A_126), k6_relat_1(A_51))=k7_relat_1(k6_relat_1(A_51), A_126) | ~r1_tarski(A_51, A_99))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_769])).
% 10.70/4.09  tff(c_20422, plain, (![A_463, A_464, A_465]: (k7_relat_1(k7_relat_1(k6_relat_1(A_463), A_464), A_465)=k7_relat_1(k6_relat_1(A_463), A_465) | ~r1_tarski(A_463, A_464))), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_791])).
% 10.70/4.09  tff(c_20546, plain, (![A_429, A_430]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_429, A_430)), A_429)=k7_relat_1(k6_relat_1(A_430), A_429) | ~r1_tarski(k3_xboole_0(A_429, A_430), A_430))), inference(superposition, [status(thm), theory('equality')], [c_17630, c_20422])).
% 10.70/4.09  tff(c_20683, plain, (![A_430, A_429]: (k7_relat_1(k6_relat_1(A_430), A_429)=k6_relat_1(k3_xboole_0(A_429, A_430)))), inference(demodulation, [status(thm), theory('equality')], [c_17836, c_6938, c_20546])).
% 10.70/4.09  tff(c_46, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.70/4.09  tff(c_189, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_46])).
% 10.70/4.09  tff(c_212, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_189])).
% 10.70/4.09  tff(c_24692, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20683, c_212])).
% 10.70/4.09  tff(c_24702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17850, c_24692])).
% 10.70/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.70/4.09  
% 10.70/4.09  Inference rules
% 10.70/4.09  ----------------------
% 10.70/4.09  #Ref     : 0
% 10.70/4.09  #Sup     : 6090
% 10.70/4.09  #Fact    : 0
% 10.70/4.09  #Define  : 0
% 10.70/4.09  #Split   : 2
% 10.70/4.09  #Chain   : 0
% 10.70/4.09  #Close   : 0
% 10.70/4.09  
% 10.70/4.09  Ordering : KBO
% 10.70/4.09  
% 10.70/4.09  Simplification rules
% 10.70/4.09  ----------------------
% 10.70/4.09  #Subsume      : 853
% 10.70/4.09  #Demod        : 6468
% 10.70/4.09  #Tautology    : 2200
% 10.70/4.09  #SimpNegUnit  : 0
% 10.70/4.09  #BackRed      : 42
% 10.70/4.09  
% 10.70/4.09  #Partial instantiations: 0
% 10.70/4.09  #Strategies tried      : 1
% 10.70/4.09  
% 10.70/4.09  Timing (in seconds)
% 10.70/4.09  ----------------------
% 10.70/4.09  Preprocessing        : 0.34
% 10.70/4.09  Parsing              : 0.18
% 10.70/4.09  CNF conversion       : 0.02
% 10.70/4.09  Main loop            : 2.97
% 10.70/4.09  Inferencing          : 0.80
% 10.70/4.09  Reduction            : 1.18
% 10.70/4.09  Demodulation         : 0.96
% 10.70/4.09  BG Simplification    : 0.12
% 10.70/4.09  Subsumption          : 0.71
% 10.70/4.09  Abstraction          : 0.18
% 10.70/4.09  MUC search           : 0.00
% 10.70/4.09  Cooper               : 0.00
% 10.70/4.09  Total                : 3.37
% 10.70/4.09  Index Insertion      : 0.00
% 10.70/4.10  Index Deletion       : 0.00
% 10.70/4.10  Index Matching       : 0.00
% 10.70/4.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
