%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:53 EST 2020

% Result     : Theorem 11.74s
% Output     : CNFRefutation 11.74s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 228 expanded)
%              Number of leaves         :   38 (  93 expanded)
%              Depth                    :   23
%              Number of atoms          :   94 ( 243 expanded)
%              Number of equality atoms :   69 ( 193 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_66,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_68,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k2_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_843,plain,(
    ! [A_119,B_120,C_121] : k5_xboole_0(k5_xboole_0(A_119,B_120),C_121) = k5_xboole_0(A_119,k5_xboole_0(B_120,C_121)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6772,plain,(
    ! [A_15733,B_15734] : k5_xboole_0(A_15733,k5_xboole_0(B_15734,k2_xboole_0(A_15733,B_15734))) = k3_xboole_0(A_15733,B_15734) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_843])).

tff(c_18,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_100,plain,(
    ! [B_65,A_66] : k5_xboole_0(B_65,A_66) = k5_xboole_0(A_66,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_135,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_100])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_304,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_311,plain,(
    ! [B_97] : k4_xboole_0(k1_xboole_0,B_97) = k3_xboole_0(k1_xboole_0,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_135])).

tff(c_343,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k4_xboole_0(B_100,A_99)) = k2_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_356,plain,(
    ! [B_97] : k5_xboole_0(B_97,k3_xboole_0(k1_xboole_0,B_97)) = k2_xboole_0(B_97,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_343])).

tff(c_462,plain,(
    ! [B_106] : k5_xboole_0(B_106,k3_xboole_0(k1_xboole_0,B_106)) = B_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_356])).

tff(c_518,plain,(
    ! [B_110] : k5_xboole_0(B_110,k3_xboole_0(B_110,k1_xboole_0)) = B_110 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_462])).

tff(c_528,plain,(
    ! [B_110] : k4_xboole_0(B_110,k1_xboole_0) = B_110 ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_12])).

tff(c_350,plain,(
    ! [B_100] : k4_xboole_0(B_100,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_135])).

tff(c_595,plain,(
    ! [B_112] : k2_xboole_0(k1_xboole_0,B_112) = B_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_350])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_255,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_263,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = A_16 ),
    inference(resolution,[status(thm)],[c_20,c_255])).

tff(c_699,plain,(
    ! [B_116] : k3_xboole_0(k1_xboole_0,B_116) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_263])).

tff(c_740,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_699])).

tff(c_96,plain,(
    ! [A_63,B_64] : r1_tarski(A_63,k2_xboole_0(A_63,B_64)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_99,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_96])).

tff(c_262,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(resolution,[status(thm)],[c_99,c_255])).

tff(c_320,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_304])).

tff(c_625,plain,(
    ! [A_114,B_115] : k5_xboole_0(k5_xboole_0(A_114,B_115),k2_xboole_0(A_114,B_115)) = k3_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_682,plain,(
    ! [A_12] : k5_xboole_0(k5_xboole_0(A_12,k1_xboole_0),A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_625])).

tff(c_693,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_18,c_682])).

tff(c_956,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_693])).

tff(c_987,plain,(
    ! [A_123] : k5_xboole_0(A_123,A_123) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_320])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] : k5_xboole_0(k5_xboole_0(A_18,B_19),C_20) = k5_xboole_0(A_18,k5_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_992,plain,(
    ! [A_123,C_20] : k5_xboole_0(A_123,k5_xboole_0(A_123,C_20)) = k5_xboole_0(k1_xboole_0,C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_987,c_22])).

tff(c_1023,plain,(
    ! [A_123,C_20] : k5_xboole_0(A_123,k5_xboole_0(A_123,C_20)) = C_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_992])).

tff(c_6787,plain,(
    ! [B_15734,A_15733] : k5_xboole_0(B_15734,k2_xboole_0(A_15733,B_15734)) = k5_xboole_0(A_15733,k3_xboole_0(A_15733,B_15734)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6772,c_1023])).

tff(c_6879,plain,(
    ! [B_15897,A_15898] : k5_xboole_0(B_15897,k2_xboole_0(A_15898,B_15897)) = k4_xboole_0(A_15898,B_15897) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6787])).

tff(c_7098,plain,(
    ! [B_16387,A_16388] : k5_xboole_0(B_16387,k4_xboole_0(A_16388,B_16387)) = k2_xboole_0(A_16388,B_16387) ),
    inference(superposition,[status(thm),theory(equality)],[c_6879,c_1023])).

tff(c_26,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7203,plain,(
    ! [B_16551,A_16552] : k2_xboole_0(B_16551,A_16552) = k2_xboole_0(A_16552,B_16551) ),
    inference(superposition,[status(thm),theory(equality)],[c_7098,c_26])).

tff(c_7460,plain,(
    ! [A_16715,B_16716] : r1_tarski(A_16715,k2_xboole_0(B_16716,A_16715)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7203,c_20])).

tff(c_7515,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_7460])).

tff(c_52,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_232,plain,(
    ! [A_80,B_81] : k1_enumset1(A_80,A_80,B_81) = k2_tarski(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    ! [E_31,B_26,C_27] : r2_hidden(E_31,k1_enumset1(E_31,B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_250,plain,(
    ! [A_82,B_83] : r2_hidden(A_82,k2_tarski(A_82,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_34])).

tff(c_253,plain,(
    ! [A_32] : r2_hidden(A_32,k1_tarski(A_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_250])).

tff(c_438,plain,(
    ! [C_103,B_104,A_105] :
      ( r2_hidden(C_103,B_104)
      | ~ r2_hidden(C_103,A_105)
      | ~ r1_tarski(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_455,plain,(
    ! [A_32,B_104] :
      ( r2_hidden(A_32,B_104)
      | ~ r1_tarski(k1_tarski(A_32),B_104) ) ),
    inference(resolution,[status(thm)],[c_253,c_438])).

tff(c_7607,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7515,c_455])).

tff(c_54,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1508,plain,(
    ! [E_137,C_138,B_139,A_140] :
      ( E_137 = C_138
      | E_137 = B_139
      | E_137 = A_140
      | ~ r2_hidden(E_137,k1_enumset1(A_140,B_139,C_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16469,plain,(
    ! [E_25236,B_25237,A_25238] :
      ( E_25236 = B_25237
      | E_25236 = A_25238
      | E_25236 = A_25238
      | ~ r2_hidden(E_25236,k2_tarski(A_25238,B_25237)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1508])).

tff(c_23601,plain,(
    ! [E_29339,A_29340] :
      ( E_29339 = A_29340
      | E_29339 = A_29340
      | E_29339 = A_29340
      | ~ r2_hidden(E_29339,k1_tarski(A_29340)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_16469])).

tff(c_23608,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7607,c_23601])).

tff(c_23627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_66,c_23608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:48:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.74/5.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.74/5.13  
% 11.74/5.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.74/5.13  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 11.74/5.13  
% 11.74/5.13  %Foreground sorts:
% 11.74/5.13  
% 11.74/5.13  
% 11.74/5.13  %Background operators:
% 11.74/5.13  
% 11.74/5.13  
% 11.74/5.13  %Foreground operators:
% 11.74/5.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.74/5.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.74/5.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.74/5.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.74/5.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.74/5.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.74/5.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.74/5.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.74/5.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.74/5.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.74/5.13  tff('#skF_5', type, '#skF_5': $i).
% 11.74/5.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 11.74/5.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.74/5.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.74/5.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.74/5.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.74/5.13  tff('#skF_4', type, '#skF_4': $i).
% 11.74/5.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.74/5.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.74/5.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 11.74/5.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.74/5.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.74/5.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.74/5.13  
% 11.74/5.15  tff(f_88, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 11.74/5.15  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.74/5.15  tff(f_52, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.74/5.15  tff(f_50, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.74/5.15  tff(f_46, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 11.74/5.15  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.74/5.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.74/5.15  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 11.74/5.15  tff(f_54, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.74/5.15  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.74/5.15  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.74/5.15  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.74/5.15  tff(f_73, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 11.74/5.15  tff(f_69, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 11.74/5.15  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.74/5.15  tff(c_66, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.74/5.15  tff(c_68, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.74/5.15  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.74/5.15  tff(c_24, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k2_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.74/5.15  tff(c_843, plain, (![A_119, B_120, C_121]: (k5_xboole_0(k5_xboole_0(A_119, B_120), C_121)=k5_xboole_0(A_119, k5_xboole_0(B_120, C_121)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.74/5.15  tff(c_6772, plain, (![A_15733, B_15734]: (k5_xboole_0(A_15733, k5_xboole_0(B_15734, k2_xboole_0(A_15733, B_15734)))=k3_xboole_0(A_15733, B_15734))), inference(superposition, [status(thm), theory('equality')], [c_24, c_843])).
% 11.74/5.15  tff(c_18, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.74/5.15  tff(c_100, plain, (![B_65, A_66]: (k5_xboole_0(B_65, A_66)=k5_xboole_0(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.74/5.15  tff(c_135, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, A_15)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_18, c_100])).
% 11.74/5.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.74/5.15  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.74/5.15  tff(c_304, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.74/5.15  tff(c_311, plain, (![B_97]: (k4_xboole_0(k1_xboole_0, B_97)=k3_xboole_0(k1_xboole_0, B_97))), inference(superposition, [status(thm), theory('equality')], [c_304, c_135])).
% 11.74/5.15  tff(c_343, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k4_xboole_0(B_100, A_99))=k2_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.74/5.15  tff(c_356, plain, (![B_97]: (k5_xboole_0(B_97, k3_xboole_0(k1_xboole_0, B_97))=k2_xboole_0(B_97, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_311, c_343])).
% 11.74/5.15  tff(c_462, plain, (![B_106]: (k5_xboole_0(B_106, k3_xboole_0(k1_xboole_0, B_106))=B_106)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_356])).
% 11.74/5.15  tff(c_518, plain, (![B_110]: (k5_xboole_0(B_110, k3_xboole_0(B_110, k1_xboole_0))=B_110)), inference(superposition, [status(thm), theory('equality')], [c_2, c_462])).
% 11.74/5.15  tff(c_528, plain, (![B_110]: (k4_xboole_0(B_110, k1_xboole_0)=B_110)), inference(superposition, [status(thm), theory('equality')], [c_518, c_12])).
% 11.74/5.15  tff(c_350, plain, (![B_100]: (k4_xboole_0(B_100, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_100))), inference(superposition, [status(thm), theory('equality')], [c_343, c_135])).
% 11.74/5.15  tff(c_595, plain, (![B_112]: (k2_xboole_0(k1_xboole_0, B_112)=B_112)), inference(demodulation, [status(thm), theory('equality')], [c_528, c_350])).
% 11.74/5.15  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.74/5.15  tff(c_255, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=A_85 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.74/5.15  tff(c_263, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k2_xboole_0(A_16, B_17))=A_16)), inference(resolution, [status(thm)], [c_20, c_255])).
% 11.74/5.15  tff(c_699, plain, (![B_116]: (k3_xboole_0(k1_xboole_0, B_116)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_595, c_263])).
% 11.74/5.15  tff(c_740, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_699])).
% 11.74/5.15  tff(c_96, plain, (![A_63, B_64]: (r1_tarski(A_63, k2_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.74/5.15  tff(c_99, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_96])).
% 11.74/5.15  tff(c_262, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(resolution, [status(thm)], [c_99, c_255])).
% 11.74/5.15  tff(c_320, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_262, c_304])).
% 11.74/5.15  tff(c_625, plain, (![A_114, B_115]: (k5_xboole_0(k5_xboole_0(A_114, B_115), k2_xboole_0(A_114, B_115))=k3_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.74/5.15  tff(c_682, plain, (![A_12]: (k5_xboole_0(k5_xboole_0(A_12, k1_xboole_0), A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_625])).
% 11.74/5.15  tff(c_693, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_18, c_682])).
% 11.74/5.15  tff(c_956, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_740, c_693])).
% 11.74/5.15  tff(c_987, plain, (![A_123]: (k5_xboole_0(A_123, A_123)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_956, c_320])).
% 11.74/5.15  tff(c_22, plain, (![A_18, B_19, C_20]: (k5_xboole_0(k5_xboole_0(A_18, B_19), C_20)=k5_xboole_0(A_18, k5_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.74/5.15  tff(c_992, plain, (![A_123, C_20]: (k5_xboole_0(A_123, k5_xboole_0(A_123, C_20))=k5_xboole_0(k1_xboole_0, C_20))), inference(superposition, [status(thm), theory('equality')], [c_987, c_22])).
% 11.74/5.15  tff(c_1023, plain, (![A_123, C_20]: (k5_xboole_0(A_123, k5_xboole_0(A_123, C_20))=C_20)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_992])).
% 11.74/5.15  tff(c_6787, plain, (![B_15734, A_15733]: (k5_xboole_0(B_15734, k2_xboole_0(A_15733, B_15734))=k5_xboole_0(A_15733, k3_xboole_0(A_15733, B_15734)))), inference(superposition, [status(thm), theory('equality')], [c_6772, c_1023])).
% 11.74/5.15  tff(c_6879, plain, (![B_15897, A_15898]: (k5_xboole_0(B_15897, k2_xboole_0(A_15898, B_15897))=k4_xboole_0(A_15898, B_15897))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6787])).
% 11.74/5.15  tff(c_7098, plain, (![B_16387, A_16388]: (k5_xboole_0(B_16387, k4_xboole_0(A_16388, B_16387))=k2_xboole_0(A_16388, B_16387))), inference(superposition, [status(thm), theory('equality')], [c_6879, c_1023])).
% 11.74/5.15  tff(c_26, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.74/5.15  tff(c_7203, plain, (![B_16551, A_16552]: (k2_xboole_0(B_16551, A_16552)=k2_xboole_0(A_16552, B_16551))), inference(superposition, [status(thm), theory('equality')], [c_7098, c_26])).
% 11.74/5.15  tff(c_7460, plain, (![A_16715, B_16716]: (r1_tarski(A_16715, k2_xboole_0(B_16716, A_16715)))), inference(superposition, [status(thm), theory('equality')], [c_7203, c_20])).
% 11.74/5.15  tff(c_7515, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_7460])).
% 11.74/5.15  tff(c_52, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.74/5.15  tff(c_232, plain, (![A_80, B_81]: (k1_enumset1(A_80, A_80, B_81)=k2_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.74/5.15  tff(c_34, plain, (![E_31, B_26, C_27]: (r2_hidden(E_31, k1_enumset1(E_31, B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.74/5.15  tff(c_250, plain, (![A_82, B_83]: (r2_hidden(A_82, k2_tarski(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_232, c_34])).
% 11.74/5.15  tff(c_253, plain, (![A_32]: (r2_hidden(A_32, k1_tarski(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_250])).
% 11.74/5.15  tff(c_438, plain, (![C_103, B_104, A_105]: (r2_hidden(C_103, B_104) | ~r2_hidden(C_103, A_105) | ~r1_tarski(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.74/5.15  tff(c_455, plain, (![A_32, B_104]: (r2_hidden(A_32, B_104) | ~r1_tarski(k1_tarski(A_32), B_104))), inference(resolution, [status(thm)], [c_253, c_438])).
% 11.74/5.15  tff(c_7607, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_7515, c_455])).
% 11.74/5.15  tff(c_54, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.74/5.15  tff(c_1508, plain, (![E_137, C_138, B_139, A_140]: (E_137=C_138 | E_137=B_139 | E_137=A_140 | ~r2_hidden(E_137, k1_enumset1(A_140, B_139, C_138)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.74/5.15  tff(c_16469, plain, (![E_25236, B_25237, A_25238]: (E_25236=B_25237 | E_25236=A_25238 | E_25236=A_25238 | ~r2_hidden(E_25236, k2_tarski(A_25238, B_25237)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1508])).
% 11.74/5.15  tff(c_23601, plain, (![E_29339, A_29340]: (E_29339=A_29340 | E_29339=A_29340 | E_29339=A_29340 | ~r2_hidden(E_29339, k1_tarski(A_29340)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_16469])).
% 11.74/5.15  tff(c_23608, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_7607, c_23601])).
% 11.74/5.15  tff(c_23627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_66, c_23608])).
% 11.74/5.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.74/5.15  
% 11.74/5.15  Inference rules
% 11.74/5.15  ----------------------
% 11.74/5.15  #Ref     : 0
% 11.74/5.15  #Sup     : 5104
% 11.74/5.15  #Fact    : 18
% 11.74/5.15  #Define  : 0
% 11.74/5.15  #Split   : 0
% 11.74/5.15  #Chain   : 0
% 11.74/5.15  #Close   : 0
% 11.74/5.15  
% 11.74/5.15  Ordering : KBO
% 11.74/5.15  
% 11.74/5.15  Simplification rules
% 11.74/5.15  ----------------------
% 11.74/5.15  #Subsume      : 285
% 11.74/5.15  #Demod        : 6574
% 11.74/5.15  #Tautology    : 2696
% 11.74/5.15  #SimpNegUnit  : 1
% 11.74/5.15  #BackRed      : 10
% 11.74/5.15  
% 11.74/5.15  #Partial instantiations: 9666
% 11.74/5.15  #Strategies tried      : 1
% 11.74/5.15  
% 11.74/5.15  Timing (in seconds)
% 11.74/5.15  ----------------------
% 11.74/5.15  Preprocessing        : 0.35
% 11.91/5.15  Parsing              : 0.18
% 11.91/5.15  CNF conversion       : 0.03
% 11.91/5.15  Main loop            : 3.97
% 11.91/5.15  Inferencing          : 1.02
% 11.91/5.15  Reduction            : 2.23
% 11.91/5.15  Demodulation         : 2.03
% 11.91/5.15  BG Simplification    : 0.10
% 11.91/5.15  Subsumption          : 0.49
% 11.91/5.15  Abstraction          : 0.15
% 11.91/5.15  MUC search           : 0.00
% 11.91/5.15  Cooper               : 0.00
% 11.91/5.15  Total                : 4.36
% 11.91/5.15  Index Insertion      : 0.00
% 11.91/5.15  Index Deletion       : 0.00
% 11.91/5.15  Index Matching       : 0.00
% 11.91/5.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
