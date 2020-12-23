%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:46 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   63 (  90 expanded)
%              Number of leaves         :   34 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  95 expanded)
%              Number of equality atoms :   44 (  77 expanded)
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

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

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

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_20,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k1_xboole_0
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_235,plain,(
    ! [A_78,B_79] : k4_xboole_0(k3_xboole_0(A_78,B_79),A_78) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_159])).

tff(c_261,plain,(
    ! [B_82] : k3_xboole_0(k1_xboole_0,B_82) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_272,plain,(
    ! [B_82] : k3_xboole_0(B_82,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_2])).

tff(c_455,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_464,plain,(
    ! [B_82] : k5_xboole_0(B_82,k1_xboole_0) = k4_xboole_0(B_82,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_455])).

tff(c_476,plain,(
    ! [B_82] : k5_xboole_0(B_82,k1_xboole_0) = B_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_464])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_182,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_159])).

tff(c_482,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k4_xboole_0(B_96,A_95)) = k2_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_503,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_482])).

tff(c_583,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_503])).

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

tff(c_256,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = A_80
      | ~ r1_xboole_0(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_804,plain,(
    ! [A_126,B_127] :
      ( k4_xboole_0(k1_tarski(A_126),k1_tarski(B_127)) = k1_tarski(A_126)
      | B_127 = A_126 ) ),
    inference(resolution,[status(thm)],[c_46,c_256])).

tff(c_26,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1069,plain,(
    ! [B_163,A_164] :
      ( k5_xboole_0(k1_tarski(B_163),k1_tarski(A_164)) = k2_xboole_0(k1_tarski(B_163),k1_tarski(A_164))
      | B_163 = A_164 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_804,c_26])).

tff(c_1084,plain,(
    ! [A_165,B_166] :
      ( k2_xboole_0(k1_tarski(A_165),k1_tarski(B_166)) = k2_tarski(A_165,B_166)
      | B_166 = A_165
      | B_166 = A_165 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1069])).

tff(c_42,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_51,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_50])).

tff(c_1105,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1084,c_51])).

tff(c_1109,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1105,c_1105,c_51])).

tff(c_1112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_28,c_1109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.48  
% 3.02/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.48  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.02/1.48  
% 3.02/1.48  %Foreground sorts:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Background operators:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Foreground operators:
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.02/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.48  
% 3.02/1.49  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.02/1.49  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.02/1.49  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.02/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.02/1.49  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.02/1.49  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.02/1.49  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.02/1.49  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.02/1.49  tff(f_79, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 3.02/1.49  tff(f_74, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.02/1.49  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.02/1.49  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.02/1.49  tff(f_82, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 3.02/1.49  tff(c_20, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.02/1.49  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.02/1.49  tff(c_159, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k1_xboole_0 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.49  tff(c_235, plain, (![A_78, B_79]: (k4_xboole_0(k3_xboole_0(A_78, B_79), A_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_159])).
% 3.02/1.49  tff(c_261, plain, (![B_82]: (k3_xboole_0(k1_xboole_0, B_82)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_235, c_20])).
% 3.02/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.49  tff(c_272, plain, (![B_82]: (k3_xboole_0(B_82, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_261, c_2])).
% 3.02/1.49  tff(c_455, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.02/1.49  tff(c_464, plain, (![B_82]: (k5_xboole_0(B_82, k1_xboole_0)=k4_xboole_0(B_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_272, c_455])).
% 3.02/1.49  tff(c_476, plain, (![B_82]: (k5_xboole_0(B_82, k1_xboole_0)=B_82)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_464])).
% 3.02/1.49  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.02/1.49  tff(c_182, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_159])).
% 3.02/1.49  tff(c_482, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k4_xboole_0(B_96, A_95))=k2_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.02/1.49  tff(c_503, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_182, c_482])).
% 3.02/1.49  tff(c_583, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_476, c_503])).
% 3.02/1.49  tff(c_28, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.02/1.49  tff(c_48, plain, (![A_51, B_52]: (k5_xboole_0(k1_tarski(A_51), k1_tarski(B_52))=k2_tarski(A_51, B_52) | B_52=A_51)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.02/1.49  tff(c_46, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), k1_tarski(B_50)) | B_50=A_49)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.02/1.49  tff(c_256, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=A_80 | ~r1_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.02/1.49  tff(c_804, plain, (![A_126, B_127]: (k4_xboole_0(k1_tarski(A_126), k1_tarski(B_127))=k1_tarski(A_126) | B_127=A_126)), inference(resolution, [status(thm)], [c_46, c_256])).
% 3.02/1.49  tff(c_26, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.02/1.49  tff(c_1069, plain, (![B_163, A_164]: (k5_xboole_0(k1_tarski(B_163), k1_tarski(A_164))=k2_xboole_0(k1_tarski(B_163), k1_tarski(A_164)) | B_163=A_164)), inference(superposition, [status(thm), theory('equality')], [c_804, c_26])).
% 3.02/1.49  tff(c_1084, plain, (![A_165, B_166]: (k2_xboole_0(k1_tarski(A_165), k1_tarski(B_166))=k2_tarski(A_165, B_166) | B_166=A_165 | B_166=A_165)), inference(superposition, [status(thm), theory('equality')], [c_48, c_1069])).
% 3.02/1.49  tff(c_42, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.02/1.49  tff(c_50, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.02/1.49  tff(c_51, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_50])).
% 3.02/1.49  tff(c_1105, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1084, c_51])).
% 3.02/1.49  tff(c_1109, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1105, c_1105, c_51])).
% 3.02/1.49  tff(c_1112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_583, c_28, c_1109])).
% 3.02/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.49  
% 3.02/1.49  Inference rules
% 3.02/1.49  ----------------------
% 3.02/1.49  #Ref     : 0
% 3.02/1.49  #Sup     : 243
% 3.02/1.49  #Fact    : 0
% 3.02/1.49  #Define  : 0
% 3.02/1.49  #Split   : 0
% 3.02/1.49  #Chain   : 0
% 3.02/1.49  #Close   : 0
% 3.02/1.49  
% 3.02/1.49  Ordering : KBO
% 3.02/1.49  
% 3.02/1.49  Simplification rules
% 3.02/1.49  ----------------------
% 3.02/1.49  #Subsume      : 24
% 3.02/1.49  #Demod        : 130
% 3.02/1.49  #Tautology    : 184
% 3.02/1.49  #SimpNegUnit  : 0
% 3.02/1.49  #BackRed      : 2
% 3.02/1.49  
% 3.02/1.49  #Partial instantiations: 0
% 3.02/1.49  #Strategies tried      : 1
% 3.02/1.49  
% 3.02/1.49  Timing (in seconds)
% 3.02/1.49  ----------------------
% 3.02/1.49  Preprocessing        : 0.32
% 3.02/1.50  Parsing              : 0.17
% 3.02/1.50  CNF conversion       : 0.02
% 3.02/1.50  Main loop            : 0.39
% 3.02/1.50  Inferencing          : 0.15
% 3.02/1.50  Reduction            : 0.14
% 3.02/1.50  Demodulation         : 0.10
% 3.02/1.50  BG Simplification    : 0.02
% 3.02/1.50  Subsumption          : 0.06
% 3.02/1.50  Abstraction          : 0.02
% 3.02/1.50  MUC search           : 0.00
% 3.02/1.50  Cooper               : 0.00
% 3.02/1.50  Total                : 0.75
% 3.02/1.50  Index Insertion      : 0.00
% 3.02/1.50  Index Deletion       : 0.00
% 3.02/1.50  Index Matching       : 0.00
% 3.02/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
