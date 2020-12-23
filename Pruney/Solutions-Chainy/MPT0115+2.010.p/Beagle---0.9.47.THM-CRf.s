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
% DateTime   : Thu Dec  3 09:45:27 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   31 (  38 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  61 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(c_31,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_1'(A_18,B_19),A_18)
      | r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    ! [A_40,B_41,B_42] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_40,B_41),B_42),A_40)
      | r1_tarski(k3_xboole_0(A_40,B_41),B_42) ) ),
    inference(resolution,[status(thm)],[c_31,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [A_40,B_41] : r1_tarski(k3_xboole_0(A_40,B_41),A_40) ),
    inference(resolution,[status(thm)],[c_115,c_4])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_32,B_33,B_34] :
      ( r2_hidden('#skF_1'(A_32,B_33),B_34)
      | ~ r1_tarski(A_32,B_34)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_292,plain,(
    ! [A_73,B_74,B_75,B_76] :
      ( r2_hidden('#skF_1'(A_73,B_74),B_75)
      | ~ r1_tarski(B_76,B_75)
      | ~ r1_tarski(A_73,B_76)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_318,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_1'(A_80,B_81),'#skF_5')
      | ~ r1_tarski(A_80,'#skF_4')
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_28,c_292])).

tff(c_327,plain,(
    ! [A_82] :
      ( ~ r1_tarski(A_82,'#skF_4')
      | r1_tarski(A_82,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_318,c_4])).

tff(c_26,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_335,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_327,c_26])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:36:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.42  
% 2.31/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.43  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.31/1.43  
% 2.31/1.43  %Foreground sorts:
% 2.31/1.43  
% 2.31/1.43  
% 2.31/1.43  %Background operators:
% 2.31/1.43  
% 2.31/1.43  
% 2.31/1.43  %Foreground operators:
% 2.31/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.31/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.31/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.31/1.43  
% 2.31/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.31/1.44  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.31/1.44  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.31/1.44  tff(c_31, plain, (![A_18, B_19]: (r2_hidden('#skF_1'(A_18, B_19), A_18) | r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.44  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.44  tff(c_115, plain, (![A_40, B_41, B_42]: (r2_hidden('#skF_1'(k3_xboole_0(A_40, B_41), B_42), A_40) | r1_tarski(k3_xboole_0(A_40, B_41), B_42))), inference(resolution, [status(thm)], [c_31, c_12])).
% 2.31/1.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.44  tff(c_131, plain, (![A_40, B_41]: (r1_tarski(k3_xboole_0(A_40, B_41), A_40))), inference(resolution, [status(thm)], [c_115, c_4])).
% 2.31/1.44  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.31/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.44  tff(c_49, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.44  tff(c_76, plain, (![A_32, B_33, B_34]: (r2_hidden('#skF_1'(A_32, B_33), B_34) | ~r1_tarski(A_32, B_34) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_6, c_49])).
% 2.31/1.44  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.44  tff(c_292, plain, (![A_73, B_74, B_75, B_76]: (r2_hidden('#skF_1'(A_73, B_74), B_75) | ~r1_tarski(B_76, B_75) | ~r1_tarski(A_73, B_76) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_76, c_2])).
% 2.31/1.44  tff(c_318, plain, (![A_80, B_81]: (r2_hidden('#skF_1'(A_80, B_81), '#skF_5') | ~r1_tarski(A_80, '#skF_4') | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_28, c_292])).
% 2.31/1.44  tff(c_327, plain, (![A_82]: (~r1_tarski(A_82, '#skF_4') | r1_tarski(A_82, '#skF_5'))), inference(resolution, [status(thm)], [c_318, c_4])).
% 2.31/1.44  tff(c_26, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.31/1.44  tff(c_335, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_327, c_26])).
% 2.31/1.44  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_335])).
% 2.31/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.44  
% 2.31/1.44  Inference rules
% 2.31/1.44  ----------------------
% 2.31/1.44  #Ref     : 0
% 2.31/1.44  #Sup     : 68
% 2.31/1.44  #Fact    : 0
% 2.31/1.44  #Define  : 0
% 2.31/1.44  #Split   : 0
% 2.31/1.44  #Chain   : 0
% 2.31/1.44  #Close   : 0
% 2.31/1.44  
% 2.31/1.44  Ordering : KBO
% 2.31/1.44  
% 2.31/1.44  Simplification rules
% 2.31/1.44  ----------------------
% 2.31/1.44  #Subsume      : 8
% 2.31/1.44  #Demod        : 1
% 2.31/1.44  #Tautology    : 5
% 2.31/1.44  #SimpNegUnit  : 0
% 2.31/1.44  #BackRed      : 0
% 2.31/1.44  
% 2.31/1.44  #Partial instantiations: 0
% 2.31/1.44  #Strategies tried      : 1
% 2.31/1.44  
% 2.31/1.44  Timing (in seconds)
% 2.31/1.44  ----------------------
% 2.31/1.44  Preprocessing        : 0.32
% 2.31/1.44  Parsing              : 0.18
% 2.31/1.44  CNF conversion       : 0.02
% 2.31/1.44  Main loop            : 0.24
% 2.31/1.44  Inferencing          : 0.10
% 2.31/1.44  Reduction            : 0.05
% 2.31/1.44  Demodulation         : 0.04
% 2.31/1.44  BG Simplification    : 0.02
% 2.31/1.44  Subsumption          : 0.06
% 2.31/1.44  Abstraction          : 0.01
% 2.31/1.44  MUC search           : 0.00
% 2.31/1.44  Cooper               : 0.00
% 2.31/1.44  Total                : 0.58
% 2.31/1.44  Index Insertion      : 0.00
% 2.31/1.44  Index Deletion       : 0.00
% 2.31/1.44  Index Matching       : 0.00
% 2.31/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
