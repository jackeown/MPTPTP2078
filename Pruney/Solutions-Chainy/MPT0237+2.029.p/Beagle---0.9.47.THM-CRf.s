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
% DateTime   : Thu Dec  3 09:49:48 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 101 expanded)
%              Number of leaves         :   35 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 108 expanded)
%              Number of equality atoms :   51 (  90 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [B_64,A_65] : k3_xboole_0(B_64,A_65) = k3_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ r1_tarski(A_59,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [B_8] : k3_xboole_0(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_77])).

tff(c_119,plain,(
    ! [B_64] : k3_xboole_0(B_64,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_82])).

tff(c_430,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_439,plain,(
    ! [B_64] : k5_xboole_0(B_64,k1_xboole_0) = k4_xboole_0(B_64,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_430])).

tff(c_451,plain,(
    ! [B_64] : k5_xboole_0(B_64,k1_xboole_0) = B_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_439])).

tff(c_22,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_98,plain,(
    ! [C_61,B_62] : r1_tarski(k1_tarski(C_61),k2_tarski(B_62,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_101,plain,(
    ! [A_15] : r1_tarski(k1_tarski(A_15),k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_98])).

tff(c_292,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k1_xboole_0
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_318,plain,(
    ! [A_15] : k4_xboole_0(k1_tarski(A_15),k1_tarski(A_15)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_292])).

tff(c_474,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k4_xboole_0(B_101,A_100)) = k2_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_489,plain,(
    ! [A_15] : k2_xboole_0(k1_tarski(A_15),k1_tarski(A_15)) = k5_xboole_0(k1_tarski(A_15),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_474])).

tff(c_646,plain,(
    ! [A_113] : k2_xboole_0(k1_tarski(A_113),k1_tarski(A_113)) = k1_tarski(A_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_489])).

tff(c_263,plain,(
    ! [A_82,B_83] : k3_tarski(k2_tarski(A_82,B_83)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_272,plain,(
    ! [A_15] : k3_tarski(k1_tarski(A_15)) = k2_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_263])).

tff(c_652,plain,(
    ! [A_113] : k3_tarski(k1_tarski(k1_tarski(A_113))) = k1_tarski(A_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_272])).

tff(c_48,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(k1_tarski(A_48),k1_tarski(B_49))
      | B_49 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_245,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = A_78
      | ~ r1_xboole_0(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_755,plain,(
    ! [A_125,B_126] :
      ( k4_xboole_0(k1_tarski(A_125),k1_tarski(B_126)) = k1_tarski(A_125)
      | B_126 = A_125 ) ),
    inference(resolution,[status(thm)],[c_48,c_245])).

tff(c_20,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_858,plain,(
    ! [B_140,A_141] :
      ( k5_xboole_0(k1_tarski(B_140),k1_tarski(A_141)) = k2_xboole_0(k1_tarski(B_140),k1_tarski(A_141))
      | B_140 = A_141 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_20])).

tff(c_50,plain,(
    ! [A_50,B_51] :
      ( k5_xboole_0(k1_tarski(A_50),k1_tarski(B_51)) = k2_tarski(A_50,B_51)
      | B_51 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_873,plain,(
    ! [B_142,A_143] :
      ( k2_xboole_0(k1_tarski(B_142),k1_tarski(A_143)) = k2_tarski(B_142,A_143)
      | B_142 = A_143
      | B_142 = A_143 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_50])).

tff(c_46,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_53,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_52])).

tff(c_903,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_873,c_53])).

tff(c_918,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_903,c_53])).

tff(c_921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_272,c_22,c_918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.41  
% 2.81/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.42  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.81/1.42  
% 2.81/1.42  %Foreground sorts:
% 2.81/1.42  
% 2.81/1.42  
% 2.81/1.42  %Background operators:
% 2.81/1.42  
% 2.81/1.42  
% 2.81/1.42  %Foreground operators:
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.81/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.81/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.81/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.81/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.81/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.81/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.81/1.42  
% 2.81/1.43  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.81/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.81/1.43  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.81/1.43  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.81/1.43  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.81/1.43  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.81/1.43  tff(f_76, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.81/1.43  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.81/1.43  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.81/1.43  tff(f_78, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.81/1.43  tff(f_83, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.81/1.43  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.81/1.43  tff(f_88, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.81/1.43  tff(f_91, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.81/1.43  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.43  tff(c_103, plain, (![B_64, A_65]: (k3_xboole_0(B_64, A_65)=k3_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.43  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.43  tff(c_77, plain, (![A_59]: (k1_xboole_0=A_59 | ~r1_tarski(A_59, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.43  tff(c_82, plain, (![B_8]: (k3_xboole_0(k1_xboole_0, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_77])).
% 2.81/1.43  tff(c_119, plain, (![B_64]: (k3_xboole_0(B_64, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_103, c_82])).
% 2.81/1.43  tff(c_430, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.43  tff(c_439, plain, (![B_64]: (k5_xboole_0(B_64, k1_xboole_0)=k4_xboole_0(B_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_119, c_430])).
% 2.81/1.43  tff(c_451, plain, (![B_64]: (k5_xboole_0(B_64, k1_xboole_0)=B_64)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_439])).
% 2.81/1.43  tff(c_22, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.81/1.43  tff(c_98, plain, (![C_61, B_62]: (r1_tarski(k1_tarski(C_61), k2_tarski(B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.81/1.43  tff(c_101, plain, (![A_15]: (r1_tarski(k1_tarski(A_15), k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_98])).
% 2.81/1.43  tff(c_292, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k1_xboole_0 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.43  tff(c_318, plain, (![A_15]: (k4_xboole_0(k1_tarski(A_15), k1_tarski(A_15))=k1_xboole_0)), inference(resolution, [status(thm)], [c_101, c_292])).
% 2.81/1.43  tff(c_474, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k4_xboole_0(B_101, A_100))=k2_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.43  tff(c_489, plain, (![A_15]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(A_15))=k5_xboole_0(k1_tarski(A_15), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_318, c_474])).
% 2.81/1.43  tff(c_646, plain, (![A_113]: (k2_xboole_0(k1_tarski(A_113), k1_tarski(A_113))=k1_tarski(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_451, c_489])).
% 2.81/1.43  tff(c_263, plain, (![A_82, B_83]: (k3_tarski(k2_tarski(A_82, B_83))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.81/1.43  tff(c_272, plain, (![A_15]: (k3_tarski(k1_tarski(A_15))=k2_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_22, c_263])).
% 2.81/1.43  tff(c_652, plain, (![A_113]: (k3_tarski(k1_tarski(k1_tarski(A_113)))=k1_tarski(A_113))), inference(superposition, [status(thm), theory('equality')], [c_646, c_272])).
% 2.81/1.43  tff(c_48, plain, (![A_48, B_49]: (r1_xboole_0(k1_tarski(A_48), k1_tarski(B_49)) | B_49=A_48)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.43  tff(c_245, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=A_78 | ~r1_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.43  tff(c_755, plain, (![A_125, B_126]: (k4_xboole_0(k1_tarski(A_125), k1_tarski(B_126))=k1_tarski(A_125) | B_126=A_125)), inference(resolution, [status(thm)], [c_48, c_245])).
% 2.81/1.43  tff(c_20, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.43  tff(c_858, plain, (![B_140, A_141]: (k5_xboole_0(k1_tarski(B_140), k1_tarski(A_141))=k2_xboole_0(k1_tarski(B_140), k1_tarski(A_141)) | B_140=A_141)), inference(superposition, [status(thm), theory('equality')], [c_755, c_20])).
% 2.81/1.43  tff(c_50, plain, (![A_50, B_51]: (k5_xboole_0(k1_tarski(A_50), k1_tarski(B_51))=k2_tarski(A_50, B_51) | B_51=A_50)), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.81/1.43  tff(c_873, plain, (![B_142, A_143]: (k2_xboole_0(k1_tarski(B_142), k1_tarski(A_143))=k2_tarski(B_142, A_143) | B_142=A_143 | B_142=A_143)), inference(superposition, [status(thm), theory('equality')], [c_858, c_50])).
% 2.81/1.43  tff(c_46, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.81/1.43  tff(c_52, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.81/1.43  tff(c_53, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_52])).
% 2.81/1.43  tff(c_903, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_873, c_53])).
% 2.81/1.43  tff(c_918, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_903, c_903, c_53])).
% 2.81/1.43  tff(c_921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_652, c_272, c_22, c_918])).
% 2.81/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.43  
% 2.81/1.43  Inference rules
% 2.81/1.43  ----------------------
% 2.81/1.43  #Ref     : 0
% 2.81/1.43  #Sup     : 200
% 2.81/1.43  #Fact    : 0
% 2.81/1.43  #Define  : 0
% 2.81/1.43  #Split   : 0
% 2.81/1.43  #Chain   : 0
% 2.81/1.43  #Close   : 0
% 2.81/1.43  
% 2.81/1.43  Ordering : KBO
% 2.81/1.43  
% 2.81/1.43  Simplification rules
% 2.81/1.43  ----------------------
% 2.81/1.43  #Subsume      : 0
% 2.81/1.43  #Demod        : 113
% 2.81/1.43  #Tautology    : 171
% 2.81/1.43  #SimpNegUnit  : 0
% 2.81/1.43  #BackRed      : 1
% 2.81/1.43  
% 2.81/1.43  #Partial instantiations: 0
% 2.81/1.43  #Strategies tried      : 1
% 2.81/1.43  
% 2.81/1.43  Timing (in seconds)
% 2.81/1.43  ----------------------
% 2.81/1.43  Preprocessing        : 0.34
% 2.81/1.43  Parsing              : 0.18
% 2.81/1.43  CNF conversion       : 0.02
% 2.81/1.43  Main loop            : 0.32
% 2.81/1.43  Inferencing          : 0.12
% 2.81/1.44  Reduction            : 0.12
% 2.81/1.44  Demodulation         : 0.09
% 2.81/1.44  BG Simplification    : 0.02
% 2.81/1.44  Subsumption          : 0.04
% 2.81/1.44  Abstraction          : 0.02
% 2.81/1.44  MUC search           : 0.00
% 2.81/1.44  Cooper               : 0.00
% 2.81/1.44  Total                : 0.69
% 2.81/1.44  Index Insertion      : 0.00
% 2.81/1.44  Index Deletion       : 0.00
% 2.81/1.44  Index Matching       : 0.00
% 2.81/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
