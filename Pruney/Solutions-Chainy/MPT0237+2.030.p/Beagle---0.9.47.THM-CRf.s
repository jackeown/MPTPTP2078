%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:48 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 118 expanded)
%              Number of leaves         :   35 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 129 expanded)
%              Number of equality atoms :   54 ( 103 expanded)
%              Maximal formula depth    :   10 (   3 average)
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

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_12,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_208,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k1_xboole_0
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_228,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_208])).

tff(c_307,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_319,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k2_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_307])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(A_68,B_69) = A_68
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_153,plain,(
    ! [A_70] : k3_xboole_0(k1_xboole_0,A_70) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_132])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_158,plain,(
    ! [A_70] : k3_xboole_0(A_70,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_2])).

tff(c_378,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_395,plain,(
    ! [A_70] : k5_xboole_0(A_70,k1_xboole_0) = k4_xboole_0(A_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_378])).

tff(c_409,plain,(
    ! [A_70] : k2_xboole_0(A_70,k1_xboole_0) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_14,c_395])).

tff(c_418,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_319])).

tff(c_22,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,(
    ! [B_55,C_56] : r1_tarski(k1_tarski(B_55),k2_tarski(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_77,plain,(
    ! [A_15] : r1_tarski(k1_tarski(A_15),k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_74])).

tff(c_226,plain,(
    ! [A_15] : k4_xboole_0(k1_tarski(A_15),k1_tarski(A_15)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_208])).

tff(c_316,plain,(
    ! [A_15] : k2_xboole_0(k1_tarski(A_15),k1_tarski(A_15)) = k5_xboole_0(k1_tarski(A_15),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_307])).

tff(c_702,plain,(
    ! [A_120] : k2_xboole_0(k1_tarski(A_120),k1_tarski(A_120)) = k1_tarski(A_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_316])).

tff(c_278,plain,(
    ! [A_82,B_83] : k3_tarski(k2_tarski(A_82,B_83)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_287,plain,(
    ! [A_15] : k3_tarski(k1_tarski(A_15)) = k2_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_278])).

tff(c_708,plain,(
    ! [A_120] : k3_tarski(k1_tarski(k1_tarski(A_120))) = k1_tarski(A_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_287])).

tff(c_264,plain,(
    ! [A_78,B_79] :
      ( r1_xboole_0(k1_tarski(A_78),k1_tarski(B_79))
      | B_79 = A_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_677,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(k1_tarski(A_118),k1_tarski(B_119)) = k1_tarski(A_118)
      | B_119 = A_118 ) ),
    inference(resolution,[status(thm)],[c_264,c_16])).

tff(c_20,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_973,plain,(
    ! [B_159,A_160] :
      ( k5_xboole_0(k1_tarski(B_159),k1_tarski(A_160)) = k2_xboole_0(k1_tarski(B_159),k1_tarski(A_160))
      | B_159 = A_160 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_20])).

tff(c_50,plain,(
    ! [A_50,B_51] :
      ( k5_xboole_0(k1_tarski(A_50),k1_tarski(B_51)) = k2_tarski(A_50,B_51)
      | B_51 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1035,plain,(
    ! [B_165,A_166] :
      ( k2_xboole_0(k1_tarski(B_165),k1_tarski(A_166)) = k2_tarski(B_165,A_166)
      | B_165 = A_166
      | B_165 = A_166 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_50])).

tff(c_46,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_52,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_53,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_52])).

tff(c_1065,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_53])).

tff(c_1071,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_1065,c_53])).

tff(c_1074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_287,c_22,c_1071])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:15:37 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.53  
% 3.11/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.53  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.11/1.53  
% 3.11/1.53  %Foreground sorts:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Background operators:
% 3.11/1.53  
% 3.11/1.53  
% 3.11/1.53  %Foreground operators:
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.11/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.11/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.11/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.11/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.11/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.53  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.11/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.11/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.11/1.53  
% 3.23/1.55  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.23/1.55  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.23/1.55  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.23/1.55  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.23/1.55  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.23/1.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.23/1.55  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.23/1.55  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.23/1.55  tff(f_76, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.23/1.55  tff(f_78, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.23/1.55  tff(f_83, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.23/1.55  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.23/1.55  tff(f_88, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 3.23/1.55  tff(f_91, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 3.23/1.55  tff(c_12, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.55  tff(c_208, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k1_xboole_0 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.55  tff(c_228, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_208])).
% 3.23/1.55  tff(c_307, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.55  tff(c_319, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k2_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_228, c_307])).
% 3.23/1.55  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.55  tff(c_132, plain, (![A_68, B_69]: (k3_xboole_0(A_68, B_69)=A_68 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.55  tff(c_153, plain, (![A_70]: (k3_xboole_0(k1_xboole_0, A_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_132])).
% 3.23/1.55  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.55  tff(c_158, plain, (![A_70]: (k3_xboole_0(A_70, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_153, c_2])).
% 3.23/1.55  tff(c_378, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k4_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.23/1.55  tff(c_395, plain, (![A_70]: (k5_xboole_0(A_70, k1_xboole_0)=k4_xboole_0(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_158, c_378])).
% 3.23/1.55  tff(c_409, plain, (![A_70]: (k2_xboole_0(A_70, k1_xboole_0)=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_319, c_14, c_395])).
% 3.23/1.55  tff(c_418, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_409, c_319])).
% 3.23/1.55  tff(c_22, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.23/1.55  tff(c_74, plain, (![B_55, C_56]: (r1_tarski(k1_tarski(B_55), k2_tarski(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.55  tff(c_77, plain, (![A_15]: (r1_tarski(k1_tarski(A_15), k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_74])).
% 3.23/1.55  tff(c_226, plain, (![A_15]: (k4_xboole_0(k1_tarski(A_15), k1_tarski(A_15))=k1_xboole_0)), inference(resolution, [status(thm)], [c_77, c_208])).
% 3.23/1.55  tff(c_316, plain, (![A_15]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(A_15))=k5_xboole_0(k1_tarski(A_15), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_226, c_307])).
% 3.23/1.55  tff(c_702, plain, (![A_120]: (k2_xboole_0(k1_tarski(A_120), k1_tarski(A_120))=k1_tarski(A_120))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_316])).
% 3.23/1.55  tff(c_278, plain, (![A_82, B_83]: (k3_tarski(k2_tarski(A_82, B_83))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.23/1.55  tff(c_287, plain, (![A_15]: (k3_tarski(k1_tarski(A_15))=k2_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_22, c_278])).
% 3.23/1.55  tff(c_708, plain, (![A_120]: (k3_tarski(k1_tarski(k1_tarski(A_120)))=k1_tarski(A_120))), inference(superposition, [status(thm), theory('equality')], [c_702, c_287])).
% 3.23/1.55  tff(c_264, plain, (![A_78, B_79]: (r1_xboole_0(k1_tarski(A_78), k1_tarski(B_79)) | B_79=A_78)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.23/1.55  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.23/1.55  tff(c_677, plain, (![A_118, B_119]: (k4_xboole_0(k1_tarski(A_118), k1_tarski(B_119))=k1_tarski(A_118) | B_119=A_118)), inference(resolution, [status(thm)], [c_264, c_16])).
% 3.23/1.55  tff(c_20, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.55  tff(c_973, plain, (![B_159, A_160]: (k5_xboole_0(k1_tarski(B_159), k1_tarski(A_160))=k2_xboole_0(k1_tarski(B_159), k1_tarski(A_160)) | B_159=A_160)), inference(superposition, [status(thm), theory('equality')], [c_677, c_20])).
% 3.23/1.55  tff(c_50, plain, (![A_50, B_51]: (k5_xboole_0(k1_tarski(A_50), k1_tarski(B_51))=k2_tarski(A_50, B_51) | B_51=A_50)), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.23/1.55  tff(c_1035, plain, (![B_165, A_166]: (k2_xboole_0(k1_tarski(B_165), k1_tarski(A_166))=k2_tarski(B_165, A_166) | B_165=A_166 | B_165=A_166)), inference(superposition, [status(thm), theory('equality')], [c_973, c_50])).
% 3.23/1.55  tff(c_46, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.23/1.55  tff(c_52, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.23/1.55  tff(c_53, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_52])).
% 3.23/1.55  tff(c_1065, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1035, c_53])).
% 3.23/1.55  tff(c_1071, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_1065, c_53])).
% 3.23/1.55  tff(c_1074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_708, c_287, c_22, c_1071])).
% 3.23/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.55  
% 3.23/1.55  Inference rules
% 3.23/1.55  ----------------------
% 3.23/1.55  #Ref     : 0
% 3.23/1.55  #Sup     : 235
% 3.23/1.55  #Fact    : 0
% 3.23/1.55  #Define  : 0
% 3.23/1.55  #Split   : 0
% 3.23/1.55  #Chain   : 0
% 3.23/1.55  #Close   : 0
% 3.23/1.55  
% 3.23/1.55  Ordering : KBO
% 3.23/1.55  
% 3.23/1.55  Simplification rules
% 3.23/1.55  ----------------------
% 3.23/1.55  #Subsume      : 1
% 3.23/1.55  #Demod        : 133
% 3.23/1.55  #Tautology    : 192
% 3.23/1.55  #SimpNegUnit  : 0
% 3.23/1.55  #BackRed      : 2
% 3.23/1.55  
% 3.23/1.55  #Partial instantiations: 0
% 3.23/1.55  #Strategies tried      : 1
% 3.23/1.55  
% 3.23/1.55  Timing (in seconds)
% 3.23/1.55  ----------------------
% 3.23/1.55  Preprocessing        : 0.33
% 3.23/1.55  Parsing              : 0.18
% 3.23/1.55  CNF conversion       : 0.02
% 3.23/1.55  Main loop            : 0.45
% 3.23/1.55  Inferencing          : 0.17
% 3.23/1.55  Reduction            : 0.16
% 3.23/1.55  Demodulation         : 0.13
% 3.23/1.55  BG Simplification    : 0.02
% 3.23/1.55  Subsumption          : 0.06
% 3.23/1.55  Abstraction          : 0.02
% 3.23/1.55  MUC search           : 0.00
% 3.23/1.55  Cooper               : 0.00
% 3.23/1.55  Total                : 0.81
% 3.23/1.55  Index Insertion      : 0.00
% 3.23/1.55  Index Deletion       : 0.00
% 3.23/1.56  Index Matching       : 0.00
% 3.23/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
