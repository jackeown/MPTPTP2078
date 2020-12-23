%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:48 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   31 (  57 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  77 expanded)
%              Number of equality atoms :   20 (  55 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(k1_tarski(A_9),k1_tarski(B_10))
      | B_10 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_65,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = A_19
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(k1_tarski(A_24),k1_tarski(B_25)) = k1_tarski(A_24)
      | B_25 = A_24 ) ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_20,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_112,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_20])).

tff(c_124,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_112])).

tff(c_4,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_65])).

tff(c_54,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [B_8] : ~ r1_xboole_0(k1_tarski(B_8),k1_tarski(B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    ! [B_8] : k4_xboole_0(k1_tarski(B_8),k1_tarski(B_8)) != k1_tarski(B_8) ),
    inference(resolution,[status(thm)],[c_54,c_14])).

tff(c_137,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_63])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_77,c_124,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.27  
% 1.86/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.27  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.86/1.27  
% 1.86/1.27  %Foreground sorts:
% 1.86/1.27  
% 1.86/1.27  
% 1.86/1.27  %Background operators:
% 1.86/1.27  
% 1.86/1.27  
% 1.86/1.27  %Foreground operators:
% 1.86/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.86/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.27  
% 1.86/1.28  tff(f_60, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.86/1.28  tff(f_55, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.86/1.28  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.86/1.28  tff(f_39, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.86/1.28  tff(f_50, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.86/1.28  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.86/1.28  tff(c_16, plain, (![A_9, B_10]: (r1_xboole_0(k1_tarski(A_9), k1_tarski(B_10)) | B_10=A_9)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.86/1.28  tff(c_65, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=A_19 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.28  tff(c_98, plain, (![A_24, B_25]: (k4_xboole_0(k1_tarski(A_24), k1_tarski(B_25))=k1_tarski(A_24) | B_25=A_24)), inference(resolution, [status(thm)], [c_16, c_65])).
% 1.86/1.28  tff(c_20, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.86/1.28  tff(c_112, plain, (k1_tarski('#skF_1')=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_98, c_20])).
% 1.86/1.28  tff(c_124, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_112])).
% 1.86/1.28  tff(c_4, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.28  tff(c_77, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_65])).
% 1.86/1.28  tff(c_54, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | k4_xboole_0(A_16, B_17)!=A_16)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.28  tff(c_14, plain, (![B_8]: (~r1_xboole_0(k1_tarski(B_8), k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.86/1.28  tff(c_63, plain, (![B_8]: (k4_xboole_0(k1_tarski(B_8), k1_tarski(B_8))!=k1_tarski(B_8))), inference(resolution, [status(thm)], [c_54, c_14])).
% 1.86/1.28  tff(c_137, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_124, c_63])).
% 1.86/1.28  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_77, c_124, c_137])).
% 1.86/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.28  
% 1.86/1.28  Inference rules
% 1.86/1.28  ----------------------
% 1.86/1.28  #Ref     : 0
% 1.86/1.28  #Sup     : 33
% 1.86/1.28  #Fact    : 0
% 1.86/1.28  #Define  : 0
% 1.86/1.28  #Split   : 0
% 1.86/1.28  #Chain   : 0
% 1.86/1.28  #Close   : 0
% 1.86/1.28  
% 1.86/1.28  Ordering : KBO
% 1.86/1.28  
% 1.86/1.28  Simplification rules
% 1.86/1.28  ----------------------
% 1.86/1.28  #Subsume      : 0
% 1.86/1.28  #Demod        : 5
% 1.86/1.28  #Tautology    : 18
% 1.86/1.28  #SimpNegUnit  : 2
% 1.86/1.28  #BackRed      : 1
% 1.86/1.28  
% 1.86/1.28  #Partial instantiations: 0
% 1.86/1.28  #Strategies tried      : 1
% 1.86/1.28  
% 1.86/1.28  Timing (in seconds)
% 1.86/1.28  ----------------------
% 1.98/1.28  Preprocessing        : 0.36
% 1.98/1.28  Parsing              : 0.20
% 1.98/1.28  CNF conversion       : 0.02
% 1.98/1.28  Main loop            : 0.11
% 1.98/1.28  Inferencing          : 0.05
% 1.98/1.28  Reduction            : 0.03
% 1.98/1.28  Demodulation         : 0.02
% 1.98/1.28  BG Simplification    : 0.01
% 1.98/1.28  Subsumption          : 0.01
% 1.98/1.28  Abstraction          : 0.01
% 1.98/1.28  MUC search           : 0.00
% 1.98/1.28  Cooper               : 0.00
% 1.98/1.28  Total                : 0.50
% 1.98/1.28  Index Insertion      : 0.00
% 1.98/1.28  Index Deletion       : 0.00
% 1.98/1.28  Index Matching       : 0.00
% 1.98/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
