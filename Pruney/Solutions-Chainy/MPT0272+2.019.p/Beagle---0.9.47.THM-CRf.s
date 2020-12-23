%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:08 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   37 (  38 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_137,plain,(
    ! [B_34,A_35] :
      ( k3_xboole_0(B_34,k1_tarski(A_35)) = k1_tarski(A_35)
      | ~ r2_hidden(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k3_xboole_0(A_30,B_31)) = k4_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_143,plain,(
    ! [A_35,B_34] :
      ( k5_xboole_0(k1_tarski(A_35),k1_tarski(A_35)) = k4_xboole_0(k1_tarski(A_35),B_34)
      | ~ r2_hidden(A_35,B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_103])).

tff(c_167,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(k1_tarski(A_36),B_37) = k1_xboole_0
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_143])).

tff(c_24,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_181,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_24])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(k1_tarski(A_14),B_15)
      | r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_84,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_192,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(k1_tarski(A_41),B_42) = k1_tarski(A_41)
      | r2_hidden(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_18,c_84])).

tff(c_22,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_201,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_22])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.23  
% 1.95/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.23  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.95/1.23  
% 1.95/1.23  %Foreground sorts:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Background operators:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Foreground operators:
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.95/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.95/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.23  
% 1.95/1.24  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.95/1.24  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.95/1.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.95/1.24  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.95/1.24  tff(f_55, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 1.95/1.24  tff(f_46, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.95/1.24  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.95/1.24  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.24  tff(c_137, plain, (![B_34, A_35]: (k3_xboole_0(B_34, k1_tarski(A_35))=k1_tarski(A_35) | ~r2_hidden(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.95/1.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.24  tff(c_94, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k3_xboole_0(A_30, B_31))=k4_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.24  tff(c_103, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_94])).
% 1.95/1.24  tff(c_143, plain, (![A_35, B_34]: (k5_xboole_0(k1_tarski(A_35), k1_tarski(A_35))=k4_xboole_0(k1_tarski(A_35), B_34) | ~r2_hidden(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_137, c_103])).
% 1.95/1.24  tff(c_167, plain, (![A_36, B_37]: (k4_xboole_0(k1_tarski(A_36), B_37)=k1_xboole_0 | ~r2_hidden(A_36, B_37))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_143])).
% 1.95/1.24  tff(c_24, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.24  tff(c_181, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_167, c_24])).
% 1.95/1.24  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(k1_tarski(A_14), B_15) | r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.24  tff(c_84, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.24  tff(c_192, plain, (![A_41, B_42]: (k4_xboole_0(k1_tarski(A_41), B_42)=k1_tarski(A_41) | r2_hidden(A_41, B_42))), inference(resolution, [status(thm)], [c_18, c_84])).
% 1.95/1.24  tff(c_22, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.95/1.24  tff(c_201, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_192, c_22])).
% 1.95/1.24  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_201])).
% 1.95/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  Inference rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Ref     : 0
% 1.95/1.24  #Sup     : 46
% 1.95/1.24  #Fact    : 0
% 1.95/1.24  #Define  : 0
% 1.95/1.24  #Split   : 0
% 1.95/1.24  #Chain   : 0
% 1.95/1.24  #Close   : 0
% 1.95/1.24  
% 1.95/1.24  Ordering : KBO
% 1.95/1.24  
% 1.95/1.24  Simplification rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Subsume      : 1
% 1.95/1.24  #Demod        : 4
% 1.95/1.24  #Tautology    : 32
% 1.95/1.24  #SimpNegUnit  : 1
% 1.95/1.24  #BackRed      : 0
% 1.95/1.24  
% 1.95/1.24  #Partial instantiations: 0
% 1.95/1.24  #Strategies tried      : 1
% 1.95/1.24  
% 1.95/1.24  Timing (in seconds)
% 1.95/1.24  ----------------------
% 1.95/1.25  Preprocessing        : 0.30
% 1.95/1.25  Parsing              : 0.16
% 1.95/1.25  CNF conversion       : 0.01
% 1.95/1.25  Main loop            : 0.13
% 1.95/1.25  Inferencing          : 0.06
% 1.95/1.25  Reduction            : 0.04
% 1.95/1.25  Demodulation         : 0.03
% 1.95/1.25  BG Simplification    : 0.01
% 1.95/1.25  Subsumption          : 0.02
% 1.95/1.25  Abstraction          : 0.01
% 1.95/1.25  MUC search           : 0.00
% 1.95/1.25  Cooper               : 0.00
% 1.95/1.25  Total                : 0.46
% 1.95/1.25  Index Insertion      : 0.00
% 1.95/1.25  Index Deletion       : 0.00
% 1.95/1.25  Index Matching       : 0.00
% 1.95/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
