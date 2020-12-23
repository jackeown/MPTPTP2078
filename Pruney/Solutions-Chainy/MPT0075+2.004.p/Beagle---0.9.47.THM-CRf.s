%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:30 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 113 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_74,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_2'(A_36,B_37),A_36)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    ! [A_36] : r1_tarski(A_36,A_36) ),
    inference(resolution,[status(thm)],[c_74,c_8])).

tff(c_38,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_118,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(A_47),B_48)
      | ~ r1_tarski(A_47,B_48)
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_821,plain,(
    ! [A_192,B_193,B_194] :
      ( r2_hidden('#skF_1'(A_192),B_193)
      | ~ r1_tarski(B_194,B_193)
      | ~ r1_tarski(A_192,B_194)
      | v1_xboole_0(A_192) ) ),
    inference(resolution,[status(thm)],[c_118,c_6])).

tff(c_842,plain,(
    ! [A_192] :
      ( r2_hidden('#skF_1'(A_192),'#skF_5')
      | ~ r1_tarski(A_192,'#skF_7')
      | v1_xboole_0(A_192) ) ),
    inference(resolution,[status(thm)],[c_42,c_821])).

tff(c_40,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_862,plain,(
    ! [A_198] :
      ( r2_hidden('#skF_1'(A_198),'#skF_6')
      | ~ r1_tarski(A_198,'#skF_7')
      | v1_xboole_0(A_198) ) ),
    inference(resolution,[status(thm)],[c_40,c_821])).

tff(c_16,plain,(
    ! [D_15,A_10,B_11] :
      ( ~ r2_hidden(D_15,A_10)
      | r2_hidden(D_15,k2_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_269,plain,(
    ! [C_78,B_79,A_80] :
      ( ~ r2_hidden(C_78,B_79)
      | ~ r2_hidden(C_78,A_80)
      | ~ r2_hidden(C_78,k2_xboole_0(A_80,B_79))
      | ~ r1_xboole_0(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_295,plain,(
    ! [D_15,B_11,A_10] :
      ( ~ r2_hidden(D_15,B_11)
      | ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(D_15,A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_269])).

tff(c_1377,plain,(
    ! [A_237,A_238] :
      ( ~ r1_xboole_0(A_237,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_238),A_237)
      | ~ r1_tarski(A_238,'#skF_7')
      | v1_xboole_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_862,c_295])).

tff(c_1388,plain,(
    ! [A_192] :
      ( ~ r1_xboole_0('#skF_5','#skF_6')
      | ~ r1_tarski(A_192,'#skF_7')
      | v1_xboole_0(A_192) ) ),
    inference(resolution,[status(thm)],[c_842,c_1377])).

tff(c_1564,plain,(
    ! [A_240] :
      ( ~ r1_tarski(A_240,'#skF_7')
      | v1_xboole_0(A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1388])).

tff(c_1572,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_1564])).

tff(c_1577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1572])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.63  
% 3.49/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 3.49/1.63  
% 3.49/1.63  %Foreground sorts:
% 3.49/1.63  
% 3.49/1.63  
% 3.49/1.63  %Background operators:
% 3.49/1.63  
% 3.49/1.63  
% 3.49/1.63  %Foreground operators:
% 3.49/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.49/1.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.49/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.49/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.49/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.49/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.49/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.63  
% 3.49/1.64  tff(f_75, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 3.49/1.64  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.49/1.64  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.49/1.64  tff(f_47, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.49/1.64  tff(f_64, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 3.49/1.64  tff(c_44, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.49/1.64  tff(c_74, plain, (![A_36, B_37]: (r2_hidden('#skF_2'(A_36, B_37), A_36) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.49/1.64  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.49/1.64  tff(c_82, plain, (![A_36]: (r1_tarski(A_36, A_36))), inference(resolution, [status(thm)], [c_74, c_8])).
% 3.49/1.64  tff(c_38, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.49/1.64  tff(c_42, plain, (r1_tarski('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.49/1.64  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.64  tff(c_86, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.49/1.64  tff(c_118, plain, (![A_47, B_48]: (r2_hidden('#skF_1'(A_47), B_48) | ~r1_tarski(A_47, B_48) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_4, c_86])).
% 3.49/1.64  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.49/1.64  tff(c_821, plain, (![A_192, B_193, B_194]: (r2_hidden('#skF_1'(A_192), B_193) | ~r1_tarski(B_194, B_193) | ~r1_tarski(A_192, B_194) | v1_xboole_0(A_192))), inference(resolution, [status(thm)], [c_118, c_6])).
% 3.49/1.64  tff(c_842, plain, (![A_192]: (r2_hidden('#skF_1'(A_192), '#skF_5') | ~r1_tarski(A_192, '#skF_7') | v1_xboole_0(A_192))), inference(resolution, [status(thm)], [c_42, c_821])).
% 3.49/1.64  tff(c_40, plain, (r1_tarski('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.49/1.64  tff(c_862, plain, (![A_198]: (r2_hidden('#skF_1'(A_198), '#skF_6') | ~r1_tarski(A_198, '#skF_7') | v1_xboole_0(A_198))), inference(resolution, [status(thm)], [c_40, c_821])).
% 3.49/1.64  tff(c_16, plain, (![D_15, A_10, B_11]: (~r2_hidden(D_15, A_10) | r2_hidden(D_15, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.64  tff(c_269, plain, (![C_78, B_79, A_80]: (~r2_hidden(C_78, B_79) | ~r2_hidden(C_78, A_80) | ~r2_hidden(C_78, k2_xboole_0(A_80, B_79)) | ~r1_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.64  tff(c_295, plain, (![D_15, B_11, A_10]: (~r2_hidden(D_15, B_11) | ~r1_xboole_0(A_10, B_11) | ~r2_hidden(D_15, A_10))), inference(resolution, [status(thm)], [c_16, c_269])).
% 3.49/1.64  tff(c_1377, plain, (![A_237, A_238]: (~r1_xboole_0(A_237, '#skF_6') | ~r2_hidden('#skF_1'(A_238), A_237) | ~r1_tarski(A_238, '#skF_7') | v1_xboole_0(A_238))), inference(resolution, [status(thm)], [c_862, c_295])).
% 3.49/1.64  tff(c_1388, plain, (![A_192]: (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_tarski(A_192, '#skF_7') | v1_xboole_0(A_192))), inference(resolution, [status(thm)], [c_842, c_1377])).
% 3.49/1.64  tff(c_1564, plain, (![A_240]: (~r1_tarski(A_240, '#skF_7') | v1_xboole_0(A_240))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1388])).
% 3.49/1.64  tff(c_1572, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_82, c_1564])).
% 3.49/1.64  tff(c_1577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1572])).
% 3.49/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.64  
% 3.49/1.64  Inference rules
% 3.49/1.64  ----------------------
% 3.49/1.64  #Ref     : 0
% 3.49/1.64  #Sup     : 354
% 3.49/1.64  #Fact    : 4
% 3.49/1.64  #Define  : 0
% 3.49/1.64  #Split   : 2
% 3.49/1.64  #Chain   : 0
% 3.49/1.64  #Close   : 0
% 3.49/1.64  
% 3.49/1.64  Ordering : KBO
% 3.49/1.64  
% 3.49/1.64  Simplification rules
% 3.49/1.64  ----------------------
% 3.49/1.64  #Subsume      : 83
% 3.49/1.64  #Demod        : 10
% 3.49/1.64  #Tautology    : 29
% 3.49/1.64  #SimpNegUnit  : 7
% 3.49/1.64  #BackRed      : 1
% 3.49/1.64  
% 3.49/1.64  #Partial instantiations: 0
% 3.49/1.64  #Strategies tried      : 1
% 3.49/1.64  
% 3.49/1.64  Timing (in seconds)
% 3.49/1.64  ----------------------
% 3.86/1.64  Preprocessing        : 0.29
% 3.86/1.64  Parsing              : 0.16
% 3.86/1.64  CNF conversion       : 0.02
% 3.86/1.64  Main loop            : 0.56
% 3.86/1.64  Inferencing          : 0.20
% 3.86/1.64  Reduction            : 0.12
% 3.86/1.64  Demodulation         : 0.07
% 3.86/1.64  BG Simplification    : 0.03
% 3.86/1.64  Subsumption          : 0.17
% 3.86/1.64  Abstraction          : 0.03
% 3.86/1.64  MUC search           : 0.00
% 3.86/1.64  Cooper               : 0.00
% 3.86/1.64  Total                : 0.88
% 3.86/1.64  Index Insertion      : 0.00
% 3.86/1.64  Index Deletion       : 0.00
% 3.86/1.64  Index Matching       : 0.00
% 3.86/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
