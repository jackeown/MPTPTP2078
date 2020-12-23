%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:09 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   39 (  66 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  76 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r1_tarski(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_xboole_1)).

tff(c_20,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_160,plain,(
    ! [A_30,B_31] : k2_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_183,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_160])).

tff(c_189,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_183])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_43])).

tff(c_142,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(A_27,C_28)
      | ~ r1_tarski(k2_xboole_0(A_27,B_29),C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_197,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(resolution,[status(thm)],[c_46,c_142])).

tff(c_239,plain,(
    ! [B_38,A_39] : r1_tarski(B_38,k2_xboole_0(A_39,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_197])).

tff(c_248,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_239])).

tff(c_16,plain,(
    ! [A_14,C_16,B_15] :
      ( r2_xboole_0(A_14,C_16)
      | ~ r1_tarski(B_15,C_16)
      | ~ r2_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_316,plain,(
    ! [A_46] :
      ( r2_xboole_0(A_46,'#skF_1')
      | ~ r2_xboole_0(A_46,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_248,c_16])).

tff(c_320,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_316])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( ~ r2_xboole_0(B_13,A_12)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_322,plain,(
    ~ r2_xboole_0('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_320,c_14])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.64  
% 2.35/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.65  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.35/1.65  
% 2.35/1.65  %Foreground sorts:
% 2.35/1.65  
% 2.35/1.65  
% 2.35/1.65  %Background operators:
% 2.35/1.65  
% 2.35/1.65  
% 2.35/1.65  %Foreground operators:
% 2.35/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.65  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.65  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.35/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.65  
% 2.35/1.66  tff(f_56, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 2.35/1.66  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.35/1.66  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.35/1.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.35/1.66  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.35/1.66  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.35/1.66  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.35/1.66  tff(f_50, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 2.35/1.66  tff(f_44, axiom, (![A, B]: ~(r2_xboole_0(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_xboole_1)).
% 2.35/1.66  tff(c_20, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.66  tff(c_6, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.66  tff(c_18, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.66  tff(c_160, plain, (![A_30, B_31]: (k2_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.66  tff(c_183, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_160])).
% 2.35/1.66  tff(c_189, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_183])).
% 2.35/1.66  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.66  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.35/1.66  tff(c_43, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.66  tff(c_46, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_43])).
% 2.35/1.66  tff(c_142, plain, (![A_27, C_28, B_29]: (r1_tarski(A_27, C_28) | ~r1_tarski(k2_xboole_0(A_27, B_29), C_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.66  tff(c_197, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(resolution, [status(thm)], [c_46, c_142])).
% 2.35/1.66  tff(c_239, plain, (![B_38, A_39]: (r1_tarski(B_38, k2_xboole_0(A_39, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_197])).
% 2.35/1.66  tff(c_248, plain, (r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_189, c_239])).
% 2.35/1.66  tff(c_16, plain, (![A_14, C_16, B_15]: (r2_xboole_0(A_14, C_16) | ~r1_tarski(B_15, C_16) | ~r2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.35/1.66  tff(c_316, plain, (![A_46]: (r2_xboole_0(A_46, '#skF_1') | ~r2_xboole_0(A_46, '#skF_2'))), inference(resolution, [status(thm)], [c_248, c_16])).
% 2.35/1.66  tff(c_320, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_316])).
% 2.35/1.66  tff(c_14, plain, (![B_13, A_12]: (~r2_xboole_0(B_13, A_12) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.35/1.66  tff(c_322, plain, (~r2_xboole_0('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_320, c_14])).
% 2.35/1.66  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_320, c_322])).
% 2.35/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.66  
% 2.35/1.66  Inference rules
% 2.35/1.66  ----------------------
% 2.35/1.66  #Ref     : 0
% 2.35/1.66  #Sup     : 76
% 2.35/1.66  #Fact    : 0
% 2.35/1.66  #Define  : 0
% 2.35/1.66  #Split   : 0
% 2.35/1.66  #Chain   : 0
% 2.35/1.66  #Close   : 0
% 2.35/1.66  
% 2.35/1.67  Ordering : KBO
% 2.35/1.67  
% 2.35/1.67  Simplification rules
% 2.35/1.67  ----------------------
% 2.35/1.67  #Subsume      : 3
% 2.35/1.67  #Demod        : 27
% 2.35/1.67  #Tautology    : 48
% 2.35/1.67  #SimpNegUnit  : 0
% 2.35/1.67  #BackRed      : 0
% 2.35/1.67  
% 2.35/1.67  #Partial instantiations: 0
% 2.35/1.67  #Strategies tried      : 1
% 2.35/1.67  
% 2.35/1.67  Timing (in seconds)
% 2.35/1.67  ----------------------
% 2.35/1.67  Preprocessing        : 0.41
% 2.35/1.67  Parsing              : 0.23
% 2.35/1.67  CNF conversion       : 0.03
% 2.35/1.67  Main loop            : 0.32
% 2.35/1.67  Inferencing          : 0.13
% 2.35/1.67  Reduction            : 0.10
% 2.35/1.67  Demodulation         : 0.08
% 2.35/1.67  BG Simplification    : 0.02
% 2.35/1.67  Subsumption          : 0.05
% 2.35/1.67  Abstraction          : 0.01
% 2.35/1.67  MUC search           : 0.00
% 2.35/1.67  Cooper               : 0.00
% 2.35/1.67  Total                : 0.78
% 2.35/1.67  Index Insertion      : 0.00
% 2.35/1.67  Index Deletion       : 0.00
% 2.35/1.67  Index Matching       : 0.00
% 2.35/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
