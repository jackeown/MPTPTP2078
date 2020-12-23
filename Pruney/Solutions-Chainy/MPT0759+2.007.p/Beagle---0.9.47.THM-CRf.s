%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:33 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   44 (  44 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  38 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_60,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] : k6_subset_1(k1_ordinal1(A),k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(k1_tarski(A_35),B_36)
      | r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_130,plain,(
    ! [B_48,A_49] :
      ( r1_xboole_0(B_48,k1_tarski(A_49))
      | r2_hidden(A_49,B_48) ) ),
    inference(resolution,[status(thm)],[c_67,c_2])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_136,plain,(
    ! [B_48,A_49] :
      ( k4_xboole_0(B_48,k1_tarski(A_49)) = B_48
      | r2_hidden(A_49,B_48) ) ),
    inference(resolution,[status(thm)],[c_130,c_14])).

tff(c_30,plain,(
    ! [A_23] : k2_xboole_0(A_23,k1_tarski(A_23)) = k1_ordinal1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_145,plain,(
    ! [A_52,B_53] : k4_xboole_0(k2_xboole_0(A_52,B_53),B_53) = k4_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_157,plain,(
    ! [A_23] : k4_xboole_0(k1_ordinal1(A_23),k1_tarski(A_23)) = k4_xboole_0(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_145])).

tff(c_28,plain,(
    ! [A_21,B_22] : k6_subset_1(A_21,B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    k6_subset_1(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_35,plain,(
    k4_xboole_0(k1_ordinal1('#skF_1'),k1_tarski('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_34])).

tff(c_250,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_35])).

tff(c_272,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_250])).

tff(c_32,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_275,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_272,c_32])).

tff(c_279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:52:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.35  
% 2.08/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1
% 2.08/1.36  
% 2.08/1.36  %Foreground sorts:
% 2.08/1.36  
% 2.08/1.36  
% 2.08/1.36  %Background operators:
% 2.08/1.36  
% 2.08/1.36  
% 2.08/1.36  %Foreground operators:
% 2.08/1.36  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.08/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.36  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.08/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.36  
% 2.08/1.37  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.08/1.37  tff(f_54, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.08/1.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.08/1.37  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.08/1.37  tff(f_60, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.08/1.37  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.08/1.37  tff(f_58, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.08/1.37  tff(f_68, negated_conjecture, ~(![A]: (k6_subset_1(k1_ordinal1(A), k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_ordinal1)).
% 2.08/1.37  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.08/1.37  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.37  tff(c_67, plain, (![A_35, B_36]: (r1_xboole_0(k1_tarski(A_35), B_36) | r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.37  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.37  tff(c_130, plain, (![B_48, A_49]: (r1_xboole_0(B_48, k1_tarski(A_49)) | r2_hidden(A_49, B_48))), inference(resolution, [status(thm)], [c_67, c_2])).
% 2.08/1.37  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.08/1.37  tff(c_136, plain, (![B_48, A_49]: (k4_xboole_0(B_48, k1_tarski(A_49))=B_48 | r2_hidden(A_49, B_48))), inference(resolution, [status(thm)], [c_130, c_14])).
% 2.08/1.37  tff(c_30, plain, (![A_23]: (k2_xboole_0(A_23, k1_tarski(A_23))=k1_ordinal1(A_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.08/1.37  tff(c_145, plain, (![A_52, B_53]: (k4_xboole_0(k2_xboole_0(A_52, B_53), B_53)=k4_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.37  tff(c_157, plain, (![A_23]: (k4_xboole_0(k1_ordinal1(A_23), k1_tarski(A_23))=k4_xboole_0(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_145])).
% 2.08/1.37  tff(c_28, plain, (![A_21, B_22]: (k6_subset_1(A_21, B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.08/1.37  tff(c_34, plain, (k6_subset_1(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.37  tff(c_35, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_34])).
% 2.08/1.37  tff(c_250, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_35])).
% 2.08/1.37  tff(c_272, plain, (r2_hidden('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_136, c_250])).
% 2.08/1.37  tff(c_32, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.08/1.37  tff(c_275, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_272, c_32])).
% 2.08/1.37  tff(c_279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_275])).
% 2.08/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.37  
% 2.08/1.37  Inference rules
% 2.08/1.37  ----------------------
% 2.08/1.37  #Ref     : 0
% 2.08/1.37  #Sup     : 57
% 2.08/1.37  #Fact    : 0
% 2.08/1.37  #Define  : 0
% 2.08/1.37  #Split   : 1
% 2.08/1.37  #Chain   : 0
% 2.08/1.37  #Close   : 0
% 2.08/1.37  
% 2.08/1.37  Ordering : KBO
% 2.08/1.37  
% 2.08/1.37  Simplification rules
% 2.08/1.37  ----------------------
% 2.08/1.37  #Subsume      : 3
% 2.08/1.37  #Demod        : 6
% 2.08/1.37  #Tautology    : 34
% 2.08/1.37  #SimpNegUnit  : 0
% 2.08/1.37  #BackRed      : 1
% 2.08/1.37  
% 2.08/1.37  #Partial instantiations: 0
% 2.08/1.37  #Strategies tried      : 1
% 2.08/1.37  
% 2.08/1.37  Timing (in seconds)
% 2.08/1.37  ----------------------
% 2.28/1.37  Preprocessing        : 0.39
% 2.28/1.37  Parsing              : 0.23
% 2.28/1.37  CNF conversion       : 0.02
% 2.28/1.37  Main loop            : 0.21
% 2.28/1.37  Inferencing          : 0.08
% 2.28/1.37  Reduction            : 0.07
% 2.28/1.37  Demodulation         : 0.06
% 2.28/1.37  BG Simplification    : 0.02
% 2.28/1.37  Subsumption          : 0.03
% 2.28/1.37  Abstraction          : 0.01
% 2.28/1.37  MUC search           : 0.00
% 2.28/1.37  Cooper               : 0.00
% 2.28/1.37  Total                : 0.63
% 2.28/1.37  Index Insertion      : 0.00
% 2.28/1.37  Index Deletion       : 0.00
% 2.28/1.37  Index Matching       : 0.00
% 2.28/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
