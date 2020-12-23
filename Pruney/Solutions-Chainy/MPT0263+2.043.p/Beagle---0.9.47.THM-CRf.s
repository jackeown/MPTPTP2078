%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:19 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  72 expanded)
%              Number of equality atoms :   22 (  37 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_107,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(k1_tarski(A_38),B_39) = k1_xboole_0
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_97,c_32])).

tff(c_116,plain,
    ( k1_tarski('#skF_1') != k1_xboole_0
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_105])).

tff(c_123,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_162,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(k1_tarski(A_44),B_45) = k1_tarski(A_44)
      | r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_184,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_105])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_184])).

tff(c_201,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(k1_tarski(A_19),B_20) = k1_xboole_0
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_232,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | k4_xboole_0(A_48,B_49) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_319,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(k1_tarski(A_63),B_64) = k1_tarski(A_63)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_232])).

tff(c_352,plain,(
    ! [B_68,A_69] :
      ( k3_xboole_0(B_68,k1_tarski(A_69)) = k1_tarski(A_69)
      | ~ r2_hidden(A_69,B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_319])).

tff(c_30,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_368,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_33])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.40  
% 2.15/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.15/1.40  
% 2.15/1.40  %Foreground sorts:
% 2.15/1.40  
% 2.15/1.40  
% 2.15/1.40  %Background operators:
% 2.15/1.40  
% 2.15/1.40  
% 2.15/1.40  %Foreground operators:
% 2.15/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.40  
% 2.15/1.41  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.15/1.41  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.15/1.41  tff(f_61, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 2.15/1.41  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.15/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.15/1.41  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.15/1.41  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.15/1.41  tff(c_107, plain, (![A_38, B_39]: (k4_xboole_0(k1_tarski(A_38), B_39)=k1_xboole_0 | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.41  tff(c_97, plain, (![A_34, B_35]: (r1_xboole_0(A_34, B_35) | k4_xboole_0(A_34, B_35)!=A_34)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.41  tff(c_32, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.15/1.41  tff(c_105, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_97, c_32])).
% 2.15/1.41  tff(c_116, plain, (k1_tarski('#skF_1')!=k1_xboole_0 | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_107, c_105])).
% 2.15/1.41  tff(c_123, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_116])).
% 2.15/1.41  tff(c_162, plain, (![A_44, B_45]: (k4_xboole_0(k1_tarski(A_44), B_45)=k1_tarski(A_44) | r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.15/1.41  tff(c_184, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_162, c_105])).
% 2.15/1.41  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_184])).
% 2.15/1.41  tff(c_201, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_116])).
% 2.15/1.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.41  tff(c_28, plain, (![A_19, B_20]: (k4_xboole_0(k1_tarski(A_19), B_20)=k1_xboole_0 | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.41  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.41  tff(c_86, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.41  tff(c_232, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | k4_xboole_0(A_48, B_49)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_86])).
% 2.15/1.41  tff(c_319, plain, (![A_63, B_64]: (k3_xboole_0(k1_tarski(A_63), B_64)=k1_tarski(A_63) | ~r2_hidden(A_63, B_64))), inference(superposition, [status(thm), theory('equality')], [c_28, c_232])).
% 2.15/1.41  tff(c_352, plain, (![B_68, A_69]: (k3_xboole_0(B_68, k1_tarski(A_69))=k1_tarski(A_69) | ~r2_hidden(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_2, c_319])).
% 2.15/1.41  tff(c_30, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.15/1.41  tff(c_33, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 2.15/1.41  tff(c_368, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_352, c_33])).
% 2.15/1.41  tff(c_388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_201, c_368])).
% 2.15/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.41  
% 2.15/1.41  Inference rules
% 2.15/1.41  ----------------------
% 2.15/1.41  #Ref     : 0
% 2.15/1.41  #Sup     : 84
% 2.15/1.41  #Fact    : 2
% 2.15/1.41  #Define  : 0
% 2.15/1.41  #Split   : 1
% 2.15/1.41  #Chain   : 0
% 2.15/1.41  #Close   : 0
% 2.15/1.41  
% 2.15/1.41  Ordering : KBO
% 2.15/1.41  
% 2.15/1.41  Simplification rules
% 2.15/1.41  ----------------------
% 2.15/1.41  #Subsume      : 10
% 2.15/1.41  #Demod        : 4
% 2.15/1.41  #Tautology    : 34
% 2.15/1.41  #SimpNegUnit  : 1
% 2.15/1.41  #BackRed      : 0
% 2.15/1.41  
% 2.15/1.41  #Partial instantiations: 0
% 2.15/1.41  #Strategies tried      : 1
% 2.15/1.41  
% 2.15/1.41  Timing (in seconds)
% 2.15/1.41  ----------------------
% 2.15/1.41  Preprocessing        : 0.33
% 2.15/1.41  Parsing              : 0.18
% 2.15/1.41  CNF conversion       : 0.02
% 2.15/1.41  Main loop            : 0.20
% 2.15/1.41  Inferencing          : 0.08
% 2.15/1.41  Reduction            : 0.06
% 2.15/1.41  Demodulation         : 0.04
% 2.15/1.41  BG Simplification    : 0.01
% 2.15/1.41  Subsumption          : 0.03
% 2.15/1.41  Abstraction          : 0.01
% 2.15/1.41  MUC search           : 0.00
% 2.15/1.41  Cooper               : 0.00
% 2.15/1.41  Total                : 0.56
% 2.15/1.41  Index Insertion      : 0.00
% 2.15/1.41  Index Deletion       : 0.00
% 2.15/1.41  Index Matching       : 0.00
% 2.15/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
