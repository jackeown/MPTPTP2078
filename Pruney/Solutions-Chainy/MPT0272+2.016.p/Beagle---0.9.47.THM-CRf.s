%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:08 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  41 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_108,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k1_tarski(A_42),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_186,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(k1_tarski(A_56),B_57) = k1_xboole_0
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_108,c_8])).

tff(c_34,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_216,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_34])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,k1_tarski(B_24)) = A_23
      | r2_hidden(B_24,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(B_44,A_45)
      | k4_xboole_0(A_45,B_44) != A_45 ) ),
    inference(resolution,[status(thm)],[c_99,c_4])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_219,plain,(
    ! [B_58,A_59] :
      ( k4_xboole_0(B_58,A_59) = B_58
      | k4_xboole_0(A_59,B_58) != A_59 ) ),
    inference(resolution,[status(thm)],[c_117,c_12])).

tff(c_234,plain,(
    ! [B_63,A_64] :
      ( k4_xboole_0(k1_tarski(B_63),A_64) = k1_tarski(B_63)
      | r2_hidden(B_63,A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_219])).

tff(c_32,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_256,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_32])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:50:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.28  
% 1.98/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.98/1.28  
% 1.98/1.28  %Foreground sorts:
% 1.98/1.28  
% 1.98/1.28  
% 1.98/1.28  %Background operators:
% 1.98/1.28  
% 1.98/1.28  
% 1.98/1.28  %Foreground operators:
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.98/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.98/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.28  
% 1.98/1.29  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.98/1.29  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.98/1.29  tff(f_63, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 1.98/1.29  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.98/1.29  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.98/1.29  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.98/1.29  tff(c_108, plain, (![A_42, B_43]: (r1_tarski(k1_tarski(A_42), B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.98/1.29  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.29  tff(c_186, plain, (![A_56, B_57]: (k4_xboole_0(k1_tarski(A_56), B_57)=k1_xboole_0 | ~r2_hidden(A_56, B_57))), inference(resolution, [status(thm)], [c_108, c_8])).
% 1.98/1.29  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.98/1.29  tff(c_216, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_186, c_34])).
% 1.98/1.29  tff(c_30, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k1_tarski(B_24))=A_23 | r2_hidden(B_24, A_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.29  tff(c_99, plain, (![A_38, B_39]: (r1_xboole_0(A_38, B_39) | k4_xboole_0(A_38, B_39)!=A_38)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.29  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.29  tff(c_117, plain, (![B_44, A_45]: (r1_xboole_0(B_44, A_45) | k4_xboole_0(A_45, B_44)!=A_45)), inference(resolution, [status(thm)], [c_99, c_4])).
% 1.98/1.29  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.29  tff(c_219, plain, (![B_58, A_59]: (k4_xboole_0(B_58, A_59)=B_58 | k4_xboole_0(A_59, B_58)!=A_59)), inference(resolution, [status(thm)], [c_117, c_12])).
% 1.98/1.29  tff(c_234, plain, (![B_63, A_64]: (k4_xboole_0(k1_tarski(B_63), A_64)=k1_tarski(B_63) | r2_hidden(B_63, A_64))), inference(superposition, [status(thm), theory('equality')], [c_30, c_219])).
% 1.98/1.29  tff(c_32, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.98/1.29  tff(c_256, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_234, c_32])).
% 1.98/1.29  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_216, c_256])).
% 1.98/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.29  
% 1.98/1.29  Inference rules
% 1.98/1.29  ----------------------
% 1.98/1.29  #Ref     : 0
% 1.98/1.29  #Sup     : 57
% 1.98/1.29  #Fact    : 0
% 1.98/1.29  #Define  : 0
% 1.98/1.29  #Split   : 0
% 1.98/1.29  #Chain   : 0
% 1.98/1.29  #Close   : 0
% 1.98/1.29  
% 1.98/1.29  Ordering : KBO
% 1.98/1.29  
% 1.98/1.29  Simplification rules
% 1.98/1.29  ----------------------
% 1.98/1.29  #Subsume      : 3
% 1.98/1.29  #Demod        : 3
% 1.98/1.29  #Tautology    : 35
% 1.98/1.29  #SimpNegUnit  : 1
% 1.98/1.29  #BackRed      : 0
% 1.98/1.29  
% 1.98/1.29  #Partial instantiations: 0
% 1.98/1.29  #Strategies tried      : 1
% 1.98/1.29  
% 1.98/1.29  Timing (in seconds)
% 1.98/1.29  ----------------------
% 1.98/1.29  Preprocessing        : 0.30
% 1.98/1.29  Parsing              : 0.17
% 1.98/1.29  CNF conversion       : 0.02
% 1.98/1.29  Main loop            : 0.16
% 1.98/1.29  Inferencing          : 0.07
% 1.98/1.29  Reduction            : 0.05
% 1.98/1.29  Demodulation         : 0.03
% 1.98/1.29  BG Simplification    : 0.01
% 1.98/1.29  Subsumption          : 0.02
% 1.98/1.29  Abstraction          : 0.01
% 1.98/1.29  MUC search           : 0.00
% 1.98/1.29  Cooper               : 0.00
% 1.98/1.29  Total                : 0.48
% 1.98/1.29  Index Insertion      : 0.00
% 1.98/1.29  Index Deletion       : 0.00
% 1.98/1.29  Index Matching       : 0.00
% 1.98/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
