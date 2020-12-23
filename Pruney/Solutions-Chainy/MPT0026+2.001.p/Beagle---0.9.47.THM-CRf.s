%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:34 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.15s
% Verified   : 
% Statistics : Number of formulae       :   34 (  50 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  99 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C) )
       => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_1'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_44])).

tff(c_30,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_51,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_29,B_30,B_31] :
      ( r2_hidden('#skF_1'(A_29,B_30),B_31)
      | ~ r1_tarski(A_29,B_31)
      | r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_222,plain,(
    ! [A_60,B_61,B_62,B_63] :
      ( r2_hidden('#skF_1'(A_60,B_61),B_62)
      | ~ r1_tarski(B_63,B_62)
      | ~ r1_tarski(A_60,B_63)
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_237,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),'#skF_5')
      | ~ r1_tarski(A_60,'#skF_4')
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_30,c_222])).

tff(c_28,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_236,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),'#skF_6')
      | ~ r1_tarski(A_60,'#skF_4')
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_28,c_222])).

tff(c_55,plain,(
    ! [D_26,A_27,B_28] :
      ( r2_hidden(D_26,k3_xboole_0(A_27,B_28))
      | ~ r2_hidden(D_26,B_28)
      | ~ r2_hidden(D_26,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1670,plain,(
    ! [A_222,A_223,B_224] :
      ( r1_tarski(A_222,k3_xboole_0(A_223,B_224))
      | ~ r2_hidden('#skF_1'(A_222,k3_xboole_0(A_223,B_224)),B_224)
      | ~ r2_hidden('#skF_1'(A_222,k3_xboole_0(A_223,B_224)),A_223) ) ),
    inference(resolution,[status(thm)],[c_55,c_4])).

tff(c_3161,plain,(
    ! [A_271,A_272] :
      ( ~ r2_hidden('#skF_1'(A_271,k3_xboole_0(A_272,'#skF_6')),A_272)
      | ~ r1_tarski(A_271,'#skF_4')
      | r1_tarski(A_271,k3_xboole_0(A_272,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_236,c_1670])).

tff(c_3255,plain,(
    ! [A_273] :
      ( ~ r1_tarski(A_273,'#skF_4')
      | r1_tarski(A_273,k3_xboole_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_237,c_3161])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3297,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3255,c_26])).

tff(c_3317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_3297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.93  
% 5.15/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.93  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.15/1.93  
% 5.15/1.93  %Foreground sorts:
% 5.15/1.93  
% 5.15/1.93  
% 5.15/1.93  %Background operators:
% 5.15/1.93  
% 5.15/1.93  
% 5.15/1.93  %Foreground operators:
% 5.15/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.15/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.15/1.93  tff('#skF_5', type, '#skF_5': $i).
% 5.15/1.93  tff('#skF_6', type, '#skF_6': $i).
% 5.15/1.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.15/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.15/1.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.15/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.15/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.15/1.93  
% 5.15/1.94  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.15/1.94  tff(f_48, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.15/1.94  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.15/1.94  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.15/1.94  tff(c_44, plain, (![A_20, B_21]: (~r2_hidden('#skF_1'(A_20, B_21), B_21) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.15/1.94  tff(c_49, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_44])).
% 5.15/1.94  tff(c_30, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.15/1.94  tff(c_51, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.15/1.94  tff(c_72, plain, (![A_29, B_30, B_31]: (r2_hidden('#skF_1'(A_29, B_30), B_31) | ~r1_tarski(A_29, B_31) | r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_6, c_51])).
% 5.15/1.94  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.15/1.94  tff(c_222, plain, (![A_60, B_61, B_62, B_63]: (r2_hidden('#skF_1'(A_60, B_61), B_62) | ~r1_tarski(B_63, B_62) | ~r1_tarski(A_60, B_63) | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_72, c_2])).
% 5.15/1.94  tff(c_237, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), '#skF_5') | ~r1_tarski(A_60, '#skF_4') | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_30, c_222])).
% 5.15/1.94  tff(c_28, plain, (r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.15/1.94  tff(c_236, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), '#skF_6') | ~r1_tarski(A_60, '#skF_4') | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_28, c_222])).
% 5.15/1.94  tff(c_55, plain, (![D_26, A_27, B_28]: (r2_hidden(D_26, k3_xboole_0(A_27, B_28)) | ~r2_hidden(D_26, B_28) | ~r2_hidden(D_26, A_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.15/1.94  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.15/1.94  tff(c_1670, plain, (![A_222, A_223, B_224]: (r1_tarski(A_222, k3_xboole_0(A_223, B_224)) | ~r2_hidden('#skF_1'(A_222, k3_xboole_0(A_223, B_224)), B_224) | ~r2_hidden('#skF_1'(A_222, k3_xboole_0(A_223, B_224)), A_223))), inference(resolution, [status(thm)], [c_55, c_4])).
% 5.15/1.94  tff(c_3161, plain, (![A_271, A_272]: (~r2_hidden('#skF_1'(A_271, k3_xboole_0(A_272, '#skF_6')), A_272) | ~r1_tarski(A_271, '#skF_4') | r1_tarski(A_271, k3_xboole_0(A_272, '#skF_6')))), inference(resolution, [status(thm)], [c_236, c_1670])).
% 5.15/1.94  tff(c_3255, plain, (![A_273]: (~r1_tarski(A_273, '#skF_4') | r1_tarski(A_273, k3_xboole_0('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_237, c_3161])).
% 5.15/1.94  tff(c_26, plain, (~r1_tarski('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.15/1.94  tff(c_3297, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_3255, c_26])).
% 5.15/1.94  tff(c_3317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_3297])).
% 5.15/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.94  
% 5.15/1.94  Inference rules
% 5.15/1.94  ----------------------
% 5.15/1.94  #Ref     : 0
% 5.15/1.94  #Sup     : 874
% 5.15/1.94  #Fact    : 0
% 5.15/1.94  #Define  : 0
% 5.15/1.94  #Split   : 2
% 5.15/1.94  #Chain   : 0
% 5.15/1.94  #Close   : 0
% 5.15/1.94  
% 5.15/1.94  Ordering : KBO
% 5.15/1.94  
% 5.15/1.94  Simplification rules
% 5.15/1.94  ----------------------
% 5.15/1.94  #Subsume      : 340
% 5.15/1.94  #Demod        : 77
% 5.15/1.94  #Tautology    : 38
% 5.15/1.94  #SimpNegUnit  : 0
% 5.15/1.94  #BackRed      : 0
% 5.15/1.94  
% 5.15/1.94  #Partial instantiations: 0
% 5.15/1.94  #Strategies tried      : 1
% 5.15/1.94  
% 5.15/1.94  Timing (in seconds)
% 5.15/1.94  ----------------------
% 5.15/1.95  Preprocessing        : 0.26
% 5.15/1.95  Parsing              : 0.14
% 5.15/1.95  CNF conversion       : 0.02
% 5.15/1.95  Main loop            : 0.92
% 5.15/1.95  Inferencing          : 0.29
% 5.15/1.95  Reduction            : 0.21
% 5.15/1.95  Demodulation         : 0.14
% 5.15/1.95  BG Simplification    : 0.03
% 5.15/1.95  Subsumption          : 0.33
% 5.15/1.95  Abstraction          : 0.04
% 5.15/1.95  MUC search           : 0.00
% 5.15/1.95  Cooper               : 0.00
% 5.15/1.95  Total                : 1.21
% 5.15/1.95  Index Insertion      : 0.00
% 5.15/1.95  Index Deletion       : 0.00
% 5.15/1.95  Index Matching       : 0.00
% 5.15/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
