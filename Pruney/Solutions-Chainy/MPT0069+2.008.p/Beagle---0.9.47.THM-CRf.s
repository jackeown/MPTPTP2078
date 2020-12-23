%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:17 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  55 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_10,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [A_25,B_26,C_27] : r1_tarski(k3_xboole_0(A_25,B_26),k2_xboole_0(A_25,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    ! [A_28,C_29] : r1_tarski(A_28,k2_xboole_0(A_28,C_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_55])).

tff(c_77,plain,(
    ! [A_30] : r1_tarski(A_30,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k1_xboole_0
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_8])).

tff(c_105,plain,(
    ! [A_34,B_35] : r1_tarski(k3_xboole_0(A_34,B_35),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_55])).

tff(c_16,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_120,plain,(
    ! [B_35] : k3_xboole_0(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_16])).

tff(c_209,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_218,plain,(
    ! [B_35] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_209])).

tff(c_227,plain,(
    ! [B_35] : k4_xboole_0(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_218])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    r2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_293,plain,(
    ! [A_53,C_54,B_55] :
      ( r2_xboole_0(A_53,C_54)
      | ~ r2_xboole_0(B_55,C_54)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_297,plain,(
    ! [A_56] :
      ( r2_xboole_0(A_56,k1_xboole_0)
      | ~ r1_tarski(A_56,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_293])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_203,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden('#skF_1'(A_44,B_45),A_44)
      | ~ r2_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_208,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_4,c_203])).

tff(c_305,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_297,c_208])).

tff(c_308,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_305])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.92/1.22  
% 1.92/1.22  %Foreground sorts:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Background operators:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Foreground operators:
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.22  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.22  
% 1.92/1.23  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.92/1.23  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.92/1.23  tff(f_45, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 1.92/1.23  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.92/1.23  tff(f_49, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.92/1.23  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.92/1.23  tff(f_61, negated_conjecture, ~(![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_xboole_1)).
% 1.92/1.23  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 1.92/1.23  tff(f_35, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 1.92/1.23  tff(c_10, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.23  tff(c_12, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.23  tff(c_55, plain, (![A_25, B_26, C_27]: (r1_tarski(k3_xboole_0(A_25, B_26), k2_xboole_0(A_25, C_27)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.23  tff(c_69, plain, (![A_28, C_29]: (r1_tarski(A_28, k2_xboole_0(A_28, C_29)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_55])).
% 1.92/1.23  tff(c_77, plain, (![A_30]: (r1_tarski(A_30, A_30))), inference(superposition, [status(thm), theory('equality')], [c_10, c_69])).
% 1.92/1.23  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k1_xboole_0 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.23  tff(c_85, plain, (![A_30]: (k4_xboole_0(A_30, A_30)=k1_xboole_0)), inference(resolution, [status(thm)], [c_77, c_8])).
% 1.92/1.23  tff(c_105, plain, (![A_34, B_35]: (r1_tarski(k3_xboole_0(A_34, B_35), A_34))), inference(superposition, [status(thm), theory('equality')], [c_10, c_55])).
% 1.92/1.23  tff(c_16, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.23  tff(c_120, plain, (![B_35]: (k3_xboole_0(k1_xboole_0, B_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_105, c_16])).
% 1.92/1.23  tff(c_209, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k3_xboole_0(A_46, B_47))=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.23  tff(c_218, plain, (![B_35]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_35))), inference(superposition, [status(thm), theory('equality')], [c_120, c_209])).
% 1.92/1.23  tff(c_227, plain, (![B_35]: (k4_xboole_0(k1_xboole_0, B_35)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_218])).
% 1.92/1.23  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | k4_xboole_0(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.23  tff(c_22, plain, (r2_xboole_0('#skF_2', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.23  tff(c_293, plain, (![A_53, C_54, B_55]: (r2_xboole_0(A_53, C_54) | ~r2_xboole_0(B_55, C_54) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.23  tff(c_297, plain, (![A_56]: (r2_xboole_0(A_56, k1_xboole_0) | ~r1_tarski(A_56, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_293])).
% 1.92/1.23  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.23  tff(c_203, plain, (![A_44, B_45]: (~r2_hidden('#skF_1'(A_44, B_45), A_44) | ~r2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.23  tff(c_208, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(resolution, [status(thm)], [c_4, c_203])).
% 1.92/1.23  tff(c_305, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_297, c_208])).
% 1.92/1.23  tff(c_308, plain, (k4_xboole_0(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_305])).
% 1.92/1.23  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_308])).
% 1.92/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.23  
% 1.92/1.23  Inference rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Ref     : 0
% 1.92/1.23  #Sup     : 66
% 1.92/1.23  #Fact    : 0
% 1.92/1.23  #Define  : 0
% 1.92/1.23  #Split   : 0
% 1.92/1.23  #Chain   : 0
% 1.92/1.23  #Close   : 0
% 1.92/1.23  
% 1.92/1.23  Ordering : KBO
% 1.92/1.23  
% 1.92/1.23  Simplification rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Subsume      : 0
% 1.92/1.23  #Demod        : 22
% 1.92/1.23  #Tautology    : 50
% 1.92/1.23  #SimpNegUnit  : 0
% 1.92/1.23  #BackRed      : 0
% 1.92/1.23  
% 1.92/1.23  #Partial instantiations: 0
% 1.92/1.23  #Strategies tried      : 1
% 1.92/1.23  
% 1.92/1.23  Timing (in seconds)
% 1.92/1.23  ----------------------
% 1.92/1.23  Preprocessing        : 0.26
% 1.92/1.23  Parsing              : 0.15
% 1.92/1.23  CNF conversion       : 0.02
% 1.92/1.23  Main loop            : 0.16
% 1.92/1.23  Inferencing          : 0.07
% 1.92/1.23  Reduction            : 0.05
% 1.92/1.23  Demodulation         : 0.04
% 1.92/1.23  BG Simplification    : 0.01
% 1.92/1.23  Subsumption          : 0.02
% 1.92/1.23  Abstraction          : 0.01
% 1.92/1.23  MUC search           : 0.00
% 1.92/1.23  Cooper               : 0.00
% 1.92/1.23  Total                : 0.45
% 1.92/1.23  Index Insertion      : 0.00
% 1.92/1.23  Index Deletion       : 0.00
% 1.92/1.23  Index Matching       : 0.00
% 1.92/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
