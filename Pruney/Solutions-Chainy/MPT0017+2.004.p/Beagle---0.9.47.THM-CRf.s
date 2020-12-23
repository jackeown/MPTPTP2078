%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:30 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  37 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

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

tff(c_56,plain,(
    ! [A_1,B_2,B_24] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_24)
      | ~ r1_tarski(A_1,B_24)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_1'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [A_43,A_44,B_45] :
      ( r1_tarski(A_43,k2_xboole_0(A_44,B_45))
      | ~ r2_hidden('#skF_1'(A_43,k2_xboole_0(A_44,B_45)),B_45) ) ),
    inference(resolution,[status(thm)],[c_10,c_32])).

tff(c_145,plain,(
    ! [A_51,B_52,A_53] :
      ( ~ r1_tarski(A_51,B_52)
      | r1_tarski(A_51,k2_xboole_0(A_53,B_52)) ) ),
    inference(resolution,[status(thm)],[c_56,c_106])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_154,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_145,c_26])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:21:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.86/1.18  
% 1.86/1.18  %Foreground sorts:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Background operators:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Foreground operators:
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.86/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.86/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.86/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.18  
% 1.86/1.19  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.86/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.86/1.19  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.86/1.19  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.86/1.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.19  tff(c_49, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.19  tff(c_56, plain, (![A_1, B_2, B_24]: (r2_hidden('#skF_1'(A_1, B_2), B_24) | ~r1_tarski(A_1, B_24) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_49])).
% 1.86/1.19  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.86/1.19  tff(c_32, plain, (![A_20, B_21]: (~r2_hidden('#skF_1'(A_20, B_21), B_21) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.19  tff(c_106, plain, (![A_43, A_44, B_45]: (r1_tarski(A_43, k2_xboole_0(A_44, B_45)) | ~r2_hidden('#skF_1'(A_43, k2_xboole_0(A_44, B_45)), B_45))), inference(resolution, [status(thm)], [c_10, c_32])).
% 1.86/1.19  tff(c_145, plain, (![A_51, B_52, A_53]: (~r1_tarski(A_51, B_52) | r1_tarski(A_51, k2_xboole_0(A_53, B_52)))), inference(resolution, [status(thm)], [c_56, c_106])).
% 1.86/1.19  tff(c_26, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.86/1.19  tff(c_154, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_145, c_26])).
% 1.86/1.19  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_154])).
% 1.86/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  Inference rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Ref     : 0
% 1.86/1.19  #Sup     : 27
% 1.86/1.19  #Fact    : 0
% 1.86/1.19  #Define  : 0
% 1.86/1.19  #Split   : 0
% 1.86/1.19  #Chain   : 0
% 1.86/1.19  #Close   : 0
% 1.86/1.19  
% 1.86/1.19  Ordering : KBO
% 1.86/1.19  
% 1.86/1.19  Simplification rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Subsume      : 2
% 1.86/1.19  #Demod        : 1
% 1.86/1.19  #Tautology    : 3
% 1.86/1.19  #SimpNegUnit  : 0
% 1.86/1.19  #BackRed      : 0
% 1.86/1.19  
% 1.86/1.19  #Partial instantiations: 0
% 1.86/1.19  #Strategies tried      : 1
% 1.86/1.19  
% 1.86/1.19  Timing (in seconds)
% 1.86/1.19  ----------------------
% 1.86/1.19  Preprocessing        : 0.27
% 1.86/1.19  Parsing              : 0.14
% 1.86/1.19  CNF conversion       : 0.02
% 1.86/1.19  Main loop            : 0.16
% 1.86/1.19  Inferencing          : 0.06
% 1.86/1.19  Reduction            : 0.04
% 1.86/1.19  Demodulation         : 0.03
% 1.86/1.19  BG Simplification    : 0.01
% 1.86/1.19  Subsumption          : 0.04
% 1.86/1.19  Abstraction          : 0.01
% 1.86/1.19  MUC search           : 0.00
% 1.86/1.19  Cooper               : 0.00
% 1.86/1.19  Total                : 0.46
% 1.86/1.19  Index Insertion      : 0.00
% 1.86/1.19  Index Deletion       : 0.00
% 1.86/1.19  Index Matching       : 0.00
% 1.86/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
