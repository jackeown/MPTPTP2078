%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:03 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  51 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_111,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_113,plain,
    ( k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_124,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_113])).

tff(c_48,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_63,plain,(
    ! [A_29,B_28] : r1_tarski(A_29,k2_xboole_0(B_28,A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_18])).

tff(c_137,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_63])).

tff(c_32,plain,(
    ! [A_20,B_21] : r1_tarski(k1_tarski(A_20),k2_tarski(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [C_19] : r2_hidden(C_19,k1_tarski(C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_148,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_155,plain,(
    ! [C_43,B_44] :
      ( r2_hidden(C_43,B_44)
      | ~ r1_tarski(k1_tarski(C_43),B_44) ) ),
    inference(resolution,[status(thm)],[c_22,c_148])).

tff(c_176,plain,(
    ! [A_45,B_46] : r2_hidden(A_45,k2_tarski(A_45,B_46)) ),
    inference(resolution,[status(thm)],[c_32,c_155])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_209,plain,(
    ! [A_51,B_52,B_53] :
      ( r2_hidden(A_51,B_52)
      | ~ r1_tarski(k2_tarski(A_51,B_53),B_52) ) ),
    inference(resolution,[status(thm)],[c_176,c_4])).

tff(c_212,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_137,c_209])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:30:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.31  
% 1.86/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.32  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 1.86/1.32  
% 1.86/1.32  %Foreground sorts:
% 1.86/1.32  
% 1.86/1.32  
% 1.86/1.32  %Background operators:
% 1.86/1.32  
% 1.86/1.32  
% 1.86/1.32  %Foreground operators:
% 1.86/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.86/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.32  tff('#skF_5', type, '#skF_5': $i).
% 1.86/1.32  tff('#skF_6', type, '#skF_6': $i).
% 1.86/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.32  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.86/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.86/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.32  
% 2.03/1.33  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.03/1.33  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.03/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.03/1.33  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.03/1.33  tff(f_57, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.03/1.33  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.03/1.33  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.03/1.33  tff(c_34, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.03/1.33  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.33  tff(c_36, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.03/1.33  tff(c_38, plain, (r1_tarski(k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 2.03/1.33  tff(c_111, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.33  tff(c_113, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_38, c_111])).
% 2.03/1.33  tff(c_124, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_113])).
% 2.03/1.33  tff(c_48, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.33  tff(c_63, plain, (![A_29, B_28]: (r1_tarski(A_29, k2_xboole_0(B_28, A_29)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_18])).
% 2.03/1.33  tff(c_137, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_124, c_63])).
% 2.03/1.33  tff(c_32, plain, (![A_20, B_21]: (r1_tarski(k1_tarski(A_20), k2_tarski(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.03/1.33  tff(c_22, plain, (![C_19]: (r2_hidden(C_19, k1_tarski(C_19)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.03/1.33  tff(c_148, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.03/1.33  tff(c_155, plain, (![C_43, B_44]: (r2_hidden(C_43, B_44) | ~r1_tarski(k1_tarski(C_43), B_44))), inference(resolution, [status(thm)], [c_22, c_148])).
% 2.03/1.33  tff(c_176, plain, (![A_45, B_46]: (r2_hidden(A_45, k2_tarski(A_45, B_46)))), inference(resolution, [status(thm)], [c_32, c_155])).
% 2.03/1.33  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.03/1.33  tff(c_209, plain, (![A_51, B_52, B_53]: (r2_hidden(A_51, B_52) | ~r1_tarski(k2_tarski(A_51, B_53), B_52))), inference(resolution, [status(thm)], [c_176, c_4])).
% 2.03/1.33  tff(c_212, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_137, c_209])).
% 2.03/1.33  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_212])).
% 2.03/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.33  
% 2.03/1.33  Inference rules
% 2.03/1.33  ----------------------
% 2.03/1.33  #Ref     : 0
% 2.03/1.33  #Sup     : 42
% 2.03/1.33  #Fact    : 0
% 2.03/1.33  #Define  : 0
% 2.03/1.33  #Split   : 1
% 2.03/1.33  #Chain   : 0
% 2.03/1.33  #Close   : 0
% 2.03/1.33  
% 2.03/1.33  Ordering : KBO
% 2.03/1.33  
% 2.03/1.33  Simplification rules
% 2.03/1.33  ----------------------
% 2.03/1.33  #Subsume      : 0
% 2.03/1.33  #Demod        : 16
% 2.03/1.33  #Tautology    : 24
% 2.03/1.33  #SimpNegUnit  : 1
% 2.03/1.33  #BackRed      : 1
% 2.03/1.33  
% 2.03/1.33  #Partial instantiations: 0
% 2.03/1.33  #Strategies tried      : 1
% 2.03/1.33  
% 2.03/1.33  Timing (in seconds)
% 2.03/1.33  ----------------------
% 2.03/1.33  Preprocessing        : 0.26
% 2.03/1.33  Parsing              : 0.13
% 2.03/1.33  CNF conversion       : 0.02
% 2.03/1.33  Main loop            : 0.18
% 2.03/1.33  Inferencing          : 0.06
% 2.03/1.33  Reduction            : 0.06
% 2.03/1.33  Demodulation         : 0.05
% 2.03/1.33  BG Simplification    : 0.01
% 2.03/1.33  Subsumption          : 0.04
% 2.03/1.33  Abstraction          : 0.01
% 2.03/1.33  MUC search           : 0.00
% 2.03/1.33  Cooper               : 0.00
% 2.03/1.33  Total                : 0.47
% 2.03/1.33  Index Insertion      : 0.00
% 2.03/1.33  Index Deletion       : 0.00
% 2.03/1.33  Index Matching       : 0.00
% 2.03/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
