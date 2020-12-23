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
% DateTime   : Thu Dec  3 09:43:23 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   42 (  73 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   57 ( 136 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D)
          & r1_xboole_0(B,D) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_16,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ r1_xboole_0(A_20,B_21)
      | ~ r2_hidden(C_22,k3_xboole_0(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ! [A_23,B_24] :
      ( ~ r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_25])).

tff(c_40,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_36])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    ! [C_10] :
      ( ~ r1_xboole_0('#skF_5','#skF_7')
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_10])).

tff(c_48,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_44])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_150,plain,(
    ! [A_44,C_45,B_46,D_47] :
      ( r1_tarski(k3_xboole_0(A_44,C_45),k3_xboole_0(B_46,D_47))
      | ~ r1_tarski(C_45,D_47)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_217,plain,(
    ! [A_57,C_58] :
      ( r1_tarski(k3_xboole_0(A_57,C_58),k1_xboole_0)
      | ~ r1_tarski(C_58,'#skF_7')
      | ~ r1_tarski(A_57,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_150])).

tff(c_76,plain,(
    ! [C_33,B_34,A_35] :
      ( r2_hidden(C_33,B_34)
      | ~ r2_hidden(C_33,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_3'(A_38),B_39)
      | ~ r1_tarski(A_38,B_39)
      | k1_xboole_0 = A_38 ) ),
    inference(resolution,[status(thm)],[c_12,c_76])).

tff(c_108,plain,(
    ! [A_38] :
      ( ~ r1_tarski(A_38,k1_xboole_0)
      | k1_xboole_0 = A_38 ) ),
    inference(resolution,[status(thm)],[c_96,c_48])).

tff(c_230,plain,(
    ! [A_59,C_60] :
      ( k3_xboole_0(A_59,C_60) = k1_xboole_0
      | ~ r1_tarski(C_60,'#skF_7')
      | ~ r1_tarski(A_59,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_217,c_108])).

tff(c_356,plain,(
    ! [A_65] :
      ( k3_xboole_0(A_65,'#skF_6') = k1_xboole_0
      | ~ r1_tarski(A_65,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_230])).

tff(c_375,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_356])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_492,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_6'),k1_xboole_0)
    | r1_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_8])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_48,c_492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:16:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.09/1.29  
% 2.09/1.29  %Foreground sorts:
% 2.09/1.29  
% 2.09/1.29  
% 2.09/1.29  %Background operators:
% 2.09/1.29  
% 2.09/1.29  
% 2.09/1.29  %Foreground operators:
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.09/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.29  
% 2.09/1.30  tff(f_69, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 2.09/1.30  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.09/1.30  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.09/1.30  tff(f_60, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_xboole_1)).
% 2.09/1.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.09/1.30  tff(c_16, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.09/1.30  tff(c_18, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.09/1.30  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.30  tff(c_25, plain, (![A_20, B_21, C_22]: (~r1_xboole_0(A_20, B_21) | ~r2_hidden(C_22, k3_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.30  tff(c_36, plain, (![A_23, B_24]: (~r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_25])).
% 2.09/1.30  tff(c_40, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_36])).
% 2.09/1.30  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.30  tff(c_44, plain, (![C_10]: (~r1_xboole_0('#skF_5', '#skF_7') | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_10])).
% 2.09/1.30  tff(c_48, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_44])).
% 2.09/1.30  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.09/1.30  tff(c_20, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.09/1.30  tff(c_150, plain, (![A_44, C_45, B_46, D_47]: (r1_tarski(k3_xboole_0(A_44, C_45), k3_xboole_0(B_46, D_47)) | ~r1_tarski(C_45, D_47) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.30  tff(c_217, plain, (![A_57, C_58]: (r1_tarski(k3_xboole_0(A_57, C_58), k1_xboole_0) | ~r1_tarski(C_58, '#skF_7') | ~r1_tarski(A_57, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_150])).
% 2.09/1.30  tff(c_76, plain, (![C_33, B_34, A_35]: (r2_hidden(C_33, B_34) | ~r2_hidden(C_33, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.30  tff(c_96, plain, (![A_38, B_39]: (r2_hidden('#skF_3'(A_38), B_39) | ~r1_tarski(A_38, B_39) | k1_xboole_0=A_38)), inference(resolution, [status(thm)], [c_12, c_76])).
% 2.09/1.30  tff(c_108, plain, (![A_38]: (~r1_tarski(A_38, k1_xboole_0) | k1_xboole_0=A_38)), inference(resolution, [status(thm)], [c_96, c_48])).
% 2.09/1.30  tff(c_230, plain, (![A_59, C_60]: (k3_xboole_0(A_59, C_60)=k1_xboole_0 | ~r1_tarski(C_60, '#skF_7') | ~r1_tarski(A_59, '#skF_5'))), inference(resolution, [status(thm)], [c_217, c_108])).
% 2.09/1.30  tff(c_356, plain, (![A_65]: (k3_xboole_0(A_65, '#skF_6')=k1_xboole_0 | ~r1_tarski(A_65, '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_230])).
% 2.09/1.30  tff(c_375, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_356])).
% 2.09/1.30  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.30  tff(c_492, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_6'), k1_xboole_0) | r1_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_375, c_8])).
% 2.09/1.30  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_48, c_492])).
% 2.09/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  Inference rules
% 2.09/1.30  ----------------------
% 2.09/1.30  #Ref     : 0
% 2.09/1.30  #Sup     : 119
% 2.09/1.30  #Fact    : 0
% 2.09/1.30  #Define  : 0
% 2.09/1.30  #Split   : 0
% 2.09/1.30  #Chain   : 0
% 2.09/1.30  #Close   : 0
% 2.09/1.30  
% 2.09/1.30  Ordering : KBO
% 2.09/1.30  
% 2.09/1.30  Simplification rules
% 2.09/1.30  ----------------------
% 2.09/1.30  #Subsume      : 25
% 2.09/1.30  #Demod        : 44
% 2.09/1.30  #Tautology    : 43
% 2.09/1.30  #SimpNegUnit  : 7
% 2.09/1.30  #BackRed      : 0
% 2.09/1.30  
% 2.09/1.30  #Partial instantiations: 0
% 2.09/1.30  #Strategies tried      : 1
% 2.09/1.30  
% 2.09/1.30  Timing (in seconds)
% 2.09/1.30  ----------------------
% 2.09/1.30  Preprocessing        : 0.27
% 2.09/1.30  Parsing              : 0.15
% 2.09/1.30  CNF conversion       : 0.02
% 2.09/1.30  Main loop            : 0.26
% 2.09/1.30  Inferencing          : 0.11
% 2.09/1.30  Reduction            : 0.07
% 2.09/1.30  Demodulation         : 0.05
% 2.09/1.30  BG Simplification    : 0.01
% 2.09/1.30  Subsumption          : 0.05
% 2.09/1.30  Abstraction          : 0.01
% 2.09/1.30  MUC search           : 0.00
% 2.09/1.30  Cooper               : 0.00
% 2.09/1.30  Total                : 0.56
% 2.09/1.30  Index Insertion      : 0.00
% 2.09/1.30  Index Deletion       : 0.00
% 2.09/1.30  Index Matching       : 0.00
% 2.09/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
