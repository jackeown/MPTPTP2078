%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:48 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  70 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_573,plain,(
    ! [A_313,B_314,C_315] :
      ( ~ r2_hidden('#skF_1'(A_313,B_314,C_315),C_315)
      | r2_hidden('#skF_2'(A_313,B_314,C_315),C_315)
      | k3_xboole_0(A_313,B_314) = C_315 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_582,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,B_2),B_2)
      | k3_xboole_0(A_1,B_2) = B_2 ) ),
    inference(resolution,[status(thm)],[c_16,c_573])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_256,plain,(
    ! [D_63,A_64,B_65] :
      ( ~ r2_hidden(D_63,'#skF_4'(A_64,B_65))
      | ~ r2_hidden(D_63,B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1839,plain,(
    ! [A_413,B_414,B_415] :
      ( ~ r2_hidden('#skF_3'('#skF_4'(A_413,B_414),B_415),B_414)
      | ~ r2_hidden(A_413,B_414)
      | r1_xboole_0('#skF_4'(A_413,B_414),B_415) ) ),
    inference(resolution,[status(thm)],[c_24,c_256])).

tff(c_1865,plain,(
    ! [A_416,B_417] :
      ( ~ r2_hidden(A_416,B_417)
      | r1_xboole_0('#skF_4'(A_416,B_417),B_417) ) ),
    inference(resolution,[status(thm)],[c_22,c_1839])).

tff(c_131,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_4'(A_42,B_43),B_43)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    ! [B_23] :
      ( ~ r1_xboole_0(B_23,'#skF_5')
      | ~ r2_hidden(B_23,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_150,plain,(
    ! [A_42] :
      ( ~ r1_xboole_0('#skF_4'(A_42,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_42,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_131,c_34])).

tff(c_1874,plain,(
    ! [A_418] : ~ r2_hidden(A_418,'#skF_5') ),
    inference(resolution,[status(thm)],[c_1865,c_150])).

tff(c_2135,plain,(
    ! [A_423] : k3_xboole_0(A_423,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_582,c_1874])).

tff(c_79,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_89,plain,(
    ! [B_37] : k3_xboole_0(k1_xboole_0,B_37) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_28])).

tff(c_2170,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2135,c_89])).

tff(c_2196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:33:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.62  
% 3.35/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.62  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.35/1.62  
% 3.35/1.62  %Foreground sorts:
% 3.35/1.62  
% 3.35/1.62  
% 3.35/1.62  %Background operators:
% 3.35/1.62  
% 3.35/1.62  
% 3.35/1.62  %Foreground operators:
% 3.35/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.35/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.35/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.35/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.35/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.35/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.35/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.35/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.35/1.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.35/1.62  
% 3.73/1.63  tff(f_80, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.73/1.63  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.73/1.63  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.73/1.63  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 3.73/1.63  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.73/1.63  tff(f_56, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.73/1.63  tff(c_36, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.73/1.63  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.73/1.63  tff(c_573, plain, (![A_313, B_314, C_315]: (~r2_hidden('#skF_1'(A_313, B_314, C_315), C_315) | r2_hidden('#skF_2'(A_313, B_314, C_315), C_315) | k3_xboole_0(A_313, B_314)=C_315)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.73/1.63  tff(c_582, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, B_2), B_2) | k3_xboole_0(A_1, B_2)=B_2)), inference(resolution, [status(thm)], [c_16, c_573])).
% 3.73/1.63  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.73/1.63  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.73/1.63  tff(c_256, plain, (![D_63, A_64, B_65]: (~r2_hidden(D_63, '#skF_4'(A_64, B_65)) | ~r2_hidden(D_63, B_65) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.73/1.63  tff(c_1839, plain, (![A_413, B_414, B_415]: (~r2_hidden('#skF_3'('#skF_4'(A_413, B_414), B_415), B_414) | ~r2_hidden(A_413, B_414) | r1_xboole_0('#skF_4'(A_413, B_414), B_415))), inference(resolution, [status(thm)], [c_24, c_256])).
% 3.73/1.63  tff(c_1865, plain, (![A_416, B_417]: (~r2_hidden(A_416, B_417) | r1_xboole_0('#skF_4'(A_416, B_417), B_417))), inference(resolution, [status(thm)], [c_22, c_1839])).
% 3.73/1.63  tff(c_131, plain, (![A_42, B_43]: (r2_hidden('#skF_4'(A_42, B_43), B_43) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.73/1.63  tff(c_34, plain, (![B_23]: (~r1_xboole_0(B_23, '#skF_5') | ~r2_hidden(B_23, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.73/1.63  tff(c_150, plain, (![A_42]: (~r1_xboole_0('#skF_4'(A_42, '#skF_5'), '#skF_5') | ~r2_hidden(A_42, '#skF_5'))), inference(resolution, [status(thm)], [c_131, c_34])).
% 3.73/1.63  tff(c_1874, plain, (![A_418]: (~r2_hidden(A_418, '#skF_5'))), inference(resolution, [status(thm)], [c_1865, c_150])).
% 3.73/1.63  tff(c_2135, plain, (![A_423]: (k3_xboole_0(A_423, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_582, c_1874])).
% 3.73/1.63  tff(c_79, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.73/1.63  tff(c_28, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.73/1.63  tff(c_89, plain, (![B_37]: (k3_xboole_0(k1_xboole_0, B_37)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79, c_28])).
% 3.73/1.63  tff(c_2170, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2135, c_89])).
% 3.73/1.63  tff(c_2196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_2170])).
% 3.73/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.63  
% 3.73/1.63  Inference rules
% 3.73/1.63  ----------------------
% 3.73/1.63  #Ref     : 0
% 3.73/1.63  #Sup     : 443
% 3.73/1.63  #Fact    : 0
% 3.73/1.63  #Define  : 0
% 3.73/1.63  #Split   : 1
% 3.73/1.63  #Chain   : 0
% 3.73/1.63  #Close   : 0
% 3.73/1.63  
% 3.73/1.63  Ordering : KBO
% 3.73/1.63  
% 3.73/1.63  Simplification rules
% 3.73/1.63  ----------------------
% 3.73/1.63  #Subsume      : 101
% 3.73/1.63  #Demod        : 219
% 3.73/1.63  #Tautology    : 117
% 3.73/1.63  #SimpNegUnit  : 17
% 3.73/1.63  #BackRed      : 21
% 3.73/1.63  
% 3.73/1.63  #Partial instantiations: 56
% 3.73/1.63  #Strategies tried      : 1
% 3.73/1.63  
% 3.73/1.63  Timing (in seconds)
% 3.73/1.63  ----------------------
% 3.73/1.63  Preprocessing        : 0.31
% 3.73/1.63  Parsing              : 0.16
% 3.73/1.63  CNF conversion       : 0.03
% 3.73/1.63  Main loop            : 0.55
% 3.73/1.63  Inferencing          : 0.22
% 3.73/1.63  Reduction            : 0.14
% 3.73/1.63  Demodulation         : 0.10
% 3.73/1.63  BG Simplification    : 0.03
% 3.73/1.63  Subsumption          : 0.12
% 3.73/1.63  Abstraction          : 0.03
% 3.73/1.63  MUC search           : 0.00
% 3.73/1.63  Cooper               : 0.00
% 3.73/1.63  Total                : 0.89
% 3.73/1.63  Index Insertion      : 0.00
% 3.73/1.63  Index Deletion       : 0.00
% 3.73/1.63  Index Matching       : 0.00
% 3.73/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
