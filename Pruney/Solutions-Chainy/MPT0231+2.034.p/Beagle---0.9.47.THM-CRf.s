%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:19 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  45 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(c_22,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k1_tarski(A_15),k2_tarski(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [A_22,B_23] : r1_tarski(k1_tarski(A_22),k2_tarski(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_47,plain,(
    ! [A_12] : r1_tarski(k1_tarski(A_12),k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_49,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [A_12] : k2_xboole_0(k1_tarski(A_12),k1_tarski(A_12)) = k1_tarski(A_12) ),
    inference(resolution,[status(thm)],[c_47,c_49])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_49])).

tff(c_172,plain,(
    ! [A_41,B_42] : k4_xboole_0(k2_xboole_0(A_41,B_42),B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_198,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_172])).

tff(c_215,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3'))) = k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_10])).

tff(c_218,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10,c_215])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_505,plain,(
    ! [A_55] :
      ( r1_tarski(A_55,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_55,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_2])).

tff(c_514,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_505])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( B_18 = A_17
      | ~ r1_tarski(k1_tarski(A_17),k1_tarski(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_519,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_514,c_20])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:33:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.28  
% 2.05/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.28  %$ r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.05/1.28  
% 2.05/1.28  %Foreground sorts:
% 2.05/1.28  
% 2.05/1.28  
% 2.05/1.28  %Background operators:
% 2.05/1.28  
% 2.05/1.28  
% 2.05/1.28  %Foreground operators:
% 2.05/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.28  
% 2.05/1.29  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 2.05/1.29  tff(f_47, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.05/1.29  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.05/1.29  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.05/1.29  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.05/1.29  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.05/1.29  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.05/1.29  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.05/1.29  tff(c_22, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.05/1.29  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), k2_tarski(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.29  tff(c_14, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.05/1.29  tff(c_44, plain, (![A_22, B_23]: (r1_tarski(k1_tarski(A_22), k2_tarski(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.29  tff(c_47, plain, (![A_12]: (r1_tarski(k1_tarski(A_12), k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_44])).
% 2.05/1.29  tff(c_49, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.29  tff(c_62, plain, (![A_12]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(A_12))=k1_tarski(A_12))), inference(resolution, [status(thm)], [c_47, c_49])).
% 2.05/1.29  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.05/1.29  tff(c_24, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.05/1.29  tff(c_64, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_24, c_49])).
% 2.05/1.29  tff(c_172, plain, (![A_41, B_42]: (k4_xboole_0(k2_xboole_0(A_41, B_42), B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.29  tff(c_198, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_172])).
% 2.05/1.29  tff(c_215, plain, (k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3')))=k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_198, c_10])).
% 2.05/1.29  tff(c_218, plain, (k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10, c_215])).
% 2.05/1.29  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.29  tff(c_505, plain, (![A_55]: (r1_tarski(A_55, k1_tarski('#skF_3')) | ~r1_tarski(A_55, k2_tarski('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_218, c_2])).
% 2.05/1.29  tff(c_514, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_505])).
% 2.05/1.29  tff(c_20, plain, (![B_18, A_17]: (B_18=A_17 | ~r1_tarski(k1_tarski(A_17), k1_tarski(B_18)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.29  tff(c_519, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_514, c_20])).
% 2.05/1.29  tff(c_526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_519])).
% 2.05/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.29  
% 2.05/1.29  Inference rules
% 2.05/1.29  ----------------------
% 2.05/1.29  #Ref     : 0
% 2.05/1.29  #Sup     : 119
% 2.05/1.29  #Fact    : 0
% 2.05/1.29  #Define  : 0
% 2.05/1.29  #Split   : 0
% 2.05/1.29  #Chain   : 0
% 2.05/1.29  #Close   : 0
% 2.05/1.29  
% 2.05/1.29  Ordering : KBO
% 2.05/1.29  
% 2.05/1.29  Simplification rules
% 2.05/1.29  ----------------------
% 2.05/1.29  #Subsume      : 4
% 2.05/1.29  #Demod        : 51
% 2.05/1.29  #Tautology    : 86
% 2.05/1.29  #SimpNegUnit  : 1
% 2.05/1.29  #BackRed      : 1
% 2.05/1.29  
% 2.05/1.29  #Partial instantiations: 0
% 2.05/1.29  #Strategies tried      : 1
% 2.05/1.29  
% 2.05/1.29  Timing (in seconds)
% 2.05/1.29  ----------------------
% 2.05/1.29  Preprocessing        : 0.28
% 2.05/1.29  Parsing              : 0.15
% 2.05/1.29  CNF conversion       : 0.02
% 2.05/1.29  Main loop            : 0.23
% 2.05/1.29  Inferencing          : 0.09
% 2.05/1.29  Reduction            : 0.08
% 2.05/1.29  Demodulation         : 0.06
% 2.05/1.29  BG Simplification    : 0.01
% 2.05/1.29  Subsumption          : 0.03
% 2.05/1.29  Abstraction          : 0.01
% 2.05/1.29  MUC search           : 0.00
% 2.05/1.29  Cooper               : 0.00
% 2.05/1.29  Total                : 0.53
% 2.05/1.29  Index Insertion      : 0.00
% 2.05/1.29  Index Deletion       : 0.00
% 2.05/1.29  Index Matching       : 0.00
% 2.05/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
