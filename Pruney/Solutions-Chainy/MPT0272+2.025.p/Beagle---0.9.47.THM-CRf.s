%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:09 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  43 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  48 expanded)
%              Number of equality atoms :   18 (  21 expanded)
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

tff(f_60,axiom,(
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

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_32,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,k1_tarski(B_25)) = A_24
      | r2_hidden(B_25,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_87,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(A_37,B_38)
      | k4_xboole_0(A_37,B_38) != A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | k4_xboole_0(A_42,B_41) != A_42 ) ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_207,plain,(
    ! [B_64,A_65] :
      ( k4_xboole_0(B_64,A_65) = B_64
      | k4_xboole_0(A_65,B_64) != A_65 ) ),
    inference(resolution,[status(thm)],[c_104,c_12])).

tff(c_227,plain,(
    ! [B_72,A_73] :
      ( k4_xboole_0(k1_tarski(B_72),A_73) = k1_tarski(B_72)
      | r2_hidden(B_72,A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_207])).

tff(c_34,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_261,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_34])).

tff(c_16,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_275,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(k2_tarski(A_80,B_81),C_82)
      | ~ r2_hidden(B_81,C_82)
      | ~ r2_hidden(A_80,C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_313,plain,(
    ! [A_89,C_90] :
      ( r1_tarski(k1_tarski(A_89),C_90)
      | ~ r2_hidden(A_89,C_90)
      | ~ r2_hidden(A_89,C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_275])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_356,plain,(
    ! [A_94,C_95] :
      ( k4_xboole_0(k1_tarski(A_94),C_95) = k1_xboole_0
      | ~ r2_hidden(A_94,C_95) ) ),
    inference(resolution,[status(thm)],[c_313,c_8])).

tff(c_36,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_381,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_36])).

tff(c_399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_381])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:31:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.41  
% 2.21/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.21/1.41  
% 2.21/1.41  %Foreground sorts:
% 2.21/1.41  
% 2.21/1.41  
% 2.21/1.41  %Background operators:
% 2.21/1.41  
% 2.21/1.41  
% 2.21/1.41  %Foreground operators:
% 2.21/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.21/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.41  
% 2.21/1.42  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.21/1.42  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.21/1.42  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.21/1.42  tff(f_65, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 2.21/1.42  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.21/1.42  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.21/1.42  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.21/1.42  tff(c_32, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k1_tarski(B_25))=A_24 | r2_hidden(B_25, A_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.21/1.42  tff(c_87, plain, (![A_37, B_38]: (r1_xboole_0(A_37, B_38) | k4_xboole_0(A_37, B_38)!=A_37)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.21/1.42  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.42  tff(c_104, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | k4_xboole_0(A_42, B_41)!=A_42)), inference(resolution, [status(thm)], [c_87, c_4])).
% 2.21/1.42  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.21/1.42  tff(c_207, plain, (![B_64, A_65]: (k4_xboole_0(B_64, A_65)=B_64 | k4_xboole_0(A_65, B_64)!=A_65)), inference(resolution, [status(thm)], [c_104, c_12])).
% 2.21/1.42  tff(c_227, plain, (![B_72, A_73]: (k4_xboole_0(k1_tarski(B_72), A_73)=k1_tarski(B_72) | r2_hidden(B_72, A_73))), inference(superposition, [status(thm), theory('equality')], [c_32, c_207])).
% 2.21/1.42  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.21/1.42  tff(c_261, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_227, c_34])).
% 2.21/1.42  tff(c_16, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.42  tff(c_275, plain, (![A_80, B_81, C_82]: (r1_tarski(k2_tarski(A_80, B_81), C_82) | ~r2_hidden(B_81, C_82) | ~r2_hidden(A_80, C_82))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.21/1.42  tff(c_313, plain, (![A_89, C_90]: (r1_tarski(k1_tarski(A_89), C_90) | ~r2_hidden(A_89, C_90) | ~r2_hidden(A_89, C_90))), inference(superposition, [status(thm), theory('equality')], [c_16, c_275])).
% 2.21/1.42  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.42  tff(c_356, plain, (![A_94, C_95]: (k4_xboole_0(k1_tarski(A_94), C_95)=k1_xboole_0 | ~r2_hidden(A_94, C_95))), inference(resolution, [status(thm)], [c_313, c_8])).
% 2.21/1.42  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.21/1.42  tff(c_381, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_356, c_36])).
% 2.21/1.42  tff(c_399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261, c_381])).
% 2.21/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.42  
% 2.21/1.42  Inference rules
% 2.21/1.42  ----------------------
% 2.21/1.42  #Ref     : 0
% 2.21/1.42  #Sup     : 82
% 2.21/1.42  #Fact    : 2
% 2.21/1.42  #Define  : 0
% 2.21/1.42  #Split   : 0
% 2.21/1.42  #Chain   : 0
% 2.21/1.42  #Close   : 0
% 2.21/1.42  
% 2.21/1.42  Ordering : KBO
% 2.21/1.42  
% 2.21/1.42  Simplification rules
% 2.21/1.42  ----------------------
% 2.21/1.42  #Subsume      : 9
% 2.21/1.42  #Demod        : 6
% 2.21/1.42  #Tautology    : 45
% 2.21/1.42  #SimpNegUnit  : 0
% 2.21/1.42  #BackRed      : 0
% 2.21/1.42  
% 2.21/1.42  #Partial instantiations: 0
% 2.21/1.42  #Strategies tried      : 1
% 2.21/1.42  
% 2.21/1.42  Timing (in seconds)
% 2.21/1.42  ----------------------
% 2.21/1.42  Preprocessing        : 0.37
% 2.21/1.42  Parsing              : 0.18
% 2.21/1.42  CNF conversion       : 0.02
% 2.21/1.42  Main loop            : 0.21
% 2.21/1.42  Inferencing          : 0.09
% 2.21/1.42  Reduction            : 0.06
% 2.21/1.42  Demodulation         : 0.04
% 2.21/1.42  BG Simplification    : 0.02
% 2.21/1.42  Subsumption          : 0.04
% 2.21/1.42  Abstraction          : 0.01
% 2.21/1.42  MUC search           : 0.00
% 2.21/1.42  Cooper               : 0.00
% 2.21/1.42  Total                : 0.61
% 2.21/1.42  Index Insertion      : 0.00
% 2.21/1.42  Index Deletion       : 0.00
% 2.21/1.42  Index Matching       : 0.00
% 2.21/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
