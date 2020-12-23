%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:46 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 105 expanded)
%              Number of equality atoms :   44 (  79 expanded)
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

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_20,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_220,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = A_80
      | ~ r1_xboole_0(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_228,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(resolution,[status(thm)],[c_20,c_220])).

tff(c_229,plain,(
    ! [A_82] : k4_xboole_0(A_82,k1_xboole_0) = A_82 ),
    inference(resolution,[status(thm)],[c_20,c_220])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_151,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k1_xboole_0
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_173,plain,(
    ! [A_9,B_10] : k4_xboole_0(k3_xboole_0(A_9,B_10),A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_151])).

tff(c_266,plain,(
    ! [B_83] : k3_xboole_0(k1_xboole_0,B_83) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_173])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_277,plain,(
    ! [B_83] : k3_xboole_0(B_83,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_2])).

tff(c_460,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_469,plain,(
    ! [B_83] : k5_xboole_0(B_83,k1_xboole_0) = k4_xboole_0(B_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_460])).

tff(c_481,plain,(
    ! [B_83] : k5_xboole_0(B_83,k1_xboole_0) = B_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_469])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_174,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_151])).

tff(c_483,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k4_xboole_0(B_97,A_96)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_507,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_483])).

tff(c_577,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_507])).

tff(c_28,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ! [A_51,B_52] :
      ( k5_xboole_0(k1_tarski(A_51),k1_tarski(B_52)) = k2_tarski(A_51,B_52)
      | B_52 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),k1_tarski(B_50))
      | B_50 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_753,plain,(
    ! [A_123,B_124] :
      ( k4_xboole_0(k1_tarski(A_123),k1_tarski(B_124)) = k1_tarski(A_123)
      | B_124 = A_123 ) ),
    inference(resolution,[status(thm)],[c_46,c_220])).

tff(c_26,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1074,plain,(
    ! [B_164,A_165] :
      ( k5_xboole_0(k1_tarski(B_164),k1_tarski(A_165)) = k2_xboole_0(k1_tarski(B_164),k1_tarski(A_165))
      | B_164 = A_165 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_26])).

tff(c_1089,plain,(
    ! [A_166,B_167] :
      ( k2_xboole_0(k1_tarski(A_166),k1_tarski(B_167)) = k2_tarski(A_166,B_167)
      | B_167 = A_166
      | B_167 = A_166 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1074])).

tff(c_42,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_51,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_50])).

tff(c_1110,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1089,c_51])).

tff(c_1114,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_1110,c_51])).

tff(c_1117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_28,c_1114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.41  
% 2.93/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.41  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.93/1.41  
% 2.93/1.41  %Foreground sorts:
% 2.93/1.41  
% 2.93/1.41  
% 2.93/1.41  %Background operators:
% 2.93/1.41  
% 2.93/1.41  
% 2.93/1.41  %Foreground operators:
% 2.93/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.93/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.93/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.93/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.93/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.93/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.41  
% 2.93/1.42  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.93/1.42  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.93/1.42  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.93/1.42  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.93/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.93/1.42  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.93/1.42  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.93/1.42  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.93/1.42  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.93/1.42  tff(f_79, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.93/1.42  tff(f_74, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.93/1.42  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.93/1.42  tff(f_82, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.93/1.42  tff(c_20, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.93/1.42  tff(c_220, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=A_80 | ~r1_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.93/1.42  tff(c_228, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(resolution, [status(thm)], [c_20, c_220])).
% 2.93/1.42  tff(c_229, plain, (![A_82]: (k4_xboole_0(A_82, k1_xboole_0)=A_82)), inference(resolution, [status(thm)], [c_20, c_220])).
% 2.93/1.42  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.42  tff(c_151, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k1_xboole_0 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.42  tff(c_173, plain, (![A_9, B_10]: (k4_xboole_0(k3_xboole_0(A_9, B_10), A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_151])).
% 2.93/1.42  tff(c_266, plain, (![B_83]: (k3_xboole_0(k1_xboole_0, B_83)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_229, c_173])).
% 2.93/1.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.42  tff(c_277, plain, (![B_83]: (k3_xboole_0(B_83, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_266, c_2])).
% 2.93/1.42  tff(c_460, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.42  tff(c_469, plain, (![B_83]: (k5_xboole_0(B_83, k1_xboole_0)=k4_xboole_0(B_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_277, c_460])).
% 2.93/1.42  tff(c_481, plain, (![B_83]: (k5_xboole_0(B_83, k1_xboole_0)=B_83)), inference(demodulation, [status(thm), theory('equality')], [c_228, c_469])).
% 2.93/1.42  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.93/1.42  tff(c_174, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_151])).
% 2.93/1.42  tff(c_483, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k4_xboole_0(B_97, A_96))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.93/1.42  tff(c_507, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_174, c_483])).
% 2.93/1.42  tff(c_577, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_481, c_507])).
% 2.93/1.42  tff(c_28, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.93/1.42  tff(c_48, plain, (![A_51, B_52]: (k5_xboole_0(k1_tarski(A_51), k1_tarski(B_52))=k2_tarski(A_51, B_52) | B_52=A_51)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.93/1.42  tff(c_46, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), k1_tarski(B_50)) | B_50=A_49)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.93/1.42  tff(c_753, plain, (![A_123, B_124]: (k4_xboole_0(k1_tarski(A_123), k1_tarski(B_124))=k1_tarski(A_123) | B_124=A_123)), inference(resolution, [status(thm)], [c_46, c_220])).
% 2.93/1.42  tff(c_26, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.93/1.42  tff(c_1074, plain, (![B_164, A_165]: (k5_xboole_0(k1_tarski(B_164), k1_tarski(A_165))=k2_xboole_0(k1_tarski(B_164), k1_tarski(A_165)) | B_164=A_165)), inference(superposition, [status(thm), theory('equality')], [c_753, c_26])).
% 2.93/1.42  tff(c_1089, plain, (![A_166, B_167]: (k2_xboole_0(k1_tarski(A_166), k1_tarski(B_167))=k2_tarski(A_166, B_167) | B_167=A_166 | B_167=A_166)), inference(superposition, [status(thm), theory('equality')], [c_48, c_1074])).
% 2.93/1.42  tff(c_42, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.93/1.42  tff(c_50, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.93/1.42  tff(c_51, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_50])).
% 2.93/1.42  tff(c_1110, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1089, c_51])).
% 2.93/1.42  tff(c_1114, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1110, c_1110, c_51])).
% 2.93/1.42  tff(c_1117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_577, c_28, c_1114])).
% 2.93/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.42  
% 2.93/1.42  Inference rules
% 2.93/1.42  ----------------------
% 2.93/1.42  #Ref     : 0
% 2.93/1.42  #Sup     : 244
% 2.93/1.42  #Fact    : 0
% 2.93/1.42  #Define  : 0
% 2.93/1.42  #Split   : 0
% 2.93/1.42  #Chain   : 0
% 2.93/1.42  #Close   : 0
% 2.93/1.42  
% 2.93/1.42  Ordering : KBO
% 2.93/1.42  
% 2.93/1.42  Simplification rules
% 2.93/1.42  ----------------------
% 2.93/1.42  #Subsume      : 24
% 2.93/1.42  #Demod        : 130
% 2.93/1.42  #Tautology    : 184
% 2.93/1.42  #SimpNegUnit  : 0
% 2.93/1.42  #BackRed      : 2
% 2.93/1.42  
% 2.93/1.42  #Partial instantiations: 0
% 2.93/1.42  #Strategies tried      : 1
% 2.93/1.42  
% 2.93/1.42  Timing (in seconds)
% 2.93/1.42  ----------------------
% 2.93/1.43  Preprocessing        : 0.32
% 2.93/1.43  Parsing              : 0.18
% 2.93/1.43  CNF conversion       : 0.02
% 2.93/1.43  Main loop            : 0.34
% 2.93/1.43  Inferencing          : 0.13
% 2.93/1.43  Reduction            : 0.12
% 2.93/1.43  Demodulation         : 0.09
% 2.93/1.43  BG Simplification    : 0.02
% 2.93/1.43  Subsumption          : 0.05
% 2.93/1.43  Abstraction          : 0.02
% 2.93/1.43  MUC search           : 0.00
% 2.93/1.43  Cooper               : 0.00
% 2.93/1.43  Total                : 0.69
% 2.93/1.43  Index Insertion      : 0.00
% 2.93/1.43  Index Deletion       : 0.00
% 2.93/1.43  Index Matching       : 0.00
% 2.93/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
