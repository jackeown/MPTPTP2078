%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:31 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 115 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [C_27,B_28,A_29] :
      ( r2_hidden(C_27,B_28)
      | ~ r2_hidden(C_27,A_29)
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [A_1,B_2,B_28] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_28)
      | ~ r1_tarski(A_1,B_28)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_164,plain,(
    ! [A_41,B_42,B_43] :
      ( r2_hidden('#skF_1'(A_41,B_42),B_43)
      | ~ r1_tarski(A_41,B_43)
      | r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_20,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_43,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,B_23)
      | ~ r2_hidden(C_24,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_49,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,'#skF_4')
      | ~ r2_hidden(C_24,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_213,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_1'(A_47,B_48),'#skF_4')
      | ~ r1_tarski(A_47,'#skF_3')
      | r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_164,c_49])).

tff(c_325,plain,(
    ! [A_62,B_63] :
      ( ~ r1_tarski(A_62,'#skF_3')
      | ~ r1_tarski(A_62,'#skF_4')
      | r1_tarski(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_85,c_213])).

tff(c_333,plain,(
    ! [B_63] :
      ( ~ r1_tarski('#skF_5','#skF_4')
      | r1_tarski('#skF_5',B_63) ) ),
    inference(resolution,[status(thm)],[c_24,c_325])).

tff(c_343,plain,(
    ! [B_64] : r1_tarski('#skF_5',B_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_333])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_131,plain,(
    ! [A_36,B_37,B_38] :
      ( r2_hidden('#skF_2'(A_36,B_37),B_38)
      | ~ r1_tarski(B_37,B_38)
      | r1_xboole_0(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_12,c_77])).

tff(c_16,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    ! [C_24] : ~ r2_hidden(C_24,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_43])).

tff(c_155,plain,(
    ! [B_39,A_40] :
      ( ~ r1_tarski(B_39,k1_xboole_0)
      | r1_xboole_0(A_40,B_39) ) ),
    inference(resolution,[status(thm)],[c_131,c_48])).

tff(c_18,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_163,plain,(
    ! [B_39] :
      ( k1_xboole_0 = B_39
      | ~ r1_tarski(B_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_155,c_18])).

tff(c_359,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_343,c_163])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_370,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_8])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:19:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.26  
% 1.89/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.89/1.26  
% 1.89/1.26  %Foreground sorts:
% 1.89/1.26  
% 1.89/1.26  
% 1.89/1.26  %Background operators:
% 1.89/1.26  
% 1.89/1.26  
% 1.89/1.26  %Foreground operators:
% 1.89/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.26  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.89/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.26  
% 2.28/1.28  tff(f_74, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.28/1.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.28/1.28  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.28/1.28  tff(f_63, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.28/1.28  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.28/1.28  tff(c_26, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.28  tff(c_22, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.28  tff(c_24, plain, (r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.28  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.28  tff(c_77, plain, (![C_27, B_28, A_29]: (r2_hidden(C_27, B_28) | ~r2_hidden(C_27, A_29) | ~r1_tarski(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.28/1.28  tff(c_85, plain, (![A_1, B_2, B_28]: (r2_hidden('#skF_1'(A_1, B_2), B_28) | ~r1_tarski(A_1, B_28) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_77])).
% 2.28/1.28  tff(c_164, plain, (![A_41, B_42, B_43]: (r2_hidden('#skF_1'(A_41, B_42), B_43) | ~r1_tarski(A_41, B_43) | r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_6, c_77])).
% 2.28/1.28  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.28  tff(c_43, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, B_23) | ~r2_hidden(C_24, A_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.28/1.28  tff(c_49, plain, (![C_24]: (~r2_hidden(C_24, '#skF_4') | ~r2_hidden(C_24, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_43])).
% 2.28/1.28  tff(c_213, plain, (![A_47, B_48]: (~r2_hidden('#skF_1'(A_47, B_48), '#skF_4') | ~r1_tarski(A_47, '#skF_3') | r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_164, c_49])).
% 2.28/1.28  tff(c_325, plain, (![A_62, B_63]: (~r1_tarski(A_62, '#skF_3') | ~r1_tarski(A_62, '#skF_4') | r1_tarski(A_62, B_63))), inference(resolution, [status(thm)], [c_85, c_213])).
% 2.28/1.28  tff(c_333, plain, (![B_63]: (~r1_tarski('#skF_5', '#skF_4') | r1_tarski('#skF_5', B_63))), inference(resolution, [status(thm)], [c_24, c_325])).
% 2.28/1.28  tff(c_343, plain, (![B_64]: (r1_tarski('#skF_5', B_64))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_333])).
% 2.28/1.28  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.28/1.28  tff(c_131, plain, (![A_36, B_37, B_38]: (r2_hidden('#skF_2'(A_36, B_37), B_38) | ~r1_tarski(B_37, B_38) | r1_xboole_0(A_36, B_37))), inference(resolution, [status(thm)], [c_12, c_77])).
% 2.28/1.28  tff(c_16, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.28  tff(c_48, plain, (![C_24]: (~r2_hidden(C_24, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_43])).
% 2.28/1.28  tff(c_155, plain, (![B_39, A_40]: (~r1_tarski(B_39, k1_xboole_0) | r1_xboole_0(A_40, B_39))), inference(resolution, [status(thm)], [c_131, c_48])).
% 2.28/1.28  tff(c_18, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.28  tff(c_163, plain, (![B_39]: (k1_xboole_0=B_39 | ~r1_tarski(B_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_155, c_18])).
% 2.28/1.28  tff(c_359, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_343, c_163])).
% 2.28/1.28  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.28  tff(c_370, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_8])).
% 2.28/1.28  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_370])).
% 2.28/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  
% 2.28/1.28  Inference rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Ref     : 0
% 2.28/1.28  #Sup     : 67
% 2.28/1.28  #Fact    : 0
% 2.28/1.28  #Define  : 0
% 2.28/1.28  #Split   : 2
% 2.28/1.28  #Chain   : 0
% 2.28/1.28  #Close   : 0
% 2.28/1.28  
% 2.28/1.28  Ordering : KBO
% 2.28/1.28  
% 2.28/1.28  Simplification rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Subsume      : 11
% 2.28/1.28  #Demod        : 25
% 2.28/1.28  #Tautology    : 16
% 2.28/1.28  #SimpNegUnit  : 1
% 2.28/1.28  #BackRed      : 11
% 2.28/1.28  
% 2.28/1.28  #Partial instantiations: 0
% 2.28/1.28  #Strategies tried      : 1
% 2.28/1.28  
% 2.28/1.28  Timing (in seconds)
% 2.28/1.28  ----------------------
% 2.28/1.28  Preprocessing        : 0.26
% 2.28/1.28  Parsing              : 0.15
% 2.28/1.28  CNF conversion       : 0.02
% 2.28/1.28  Main loop            : 0.24
% 2.28/1.28  Inferencing          : 0.09
% 2.28/1.28  Reduction            : 0.06
% 2.28/1.28  Demodulation         : 0.04
% 2.28/1.28  BG Simplification    : 0.01
% 2.28/1.28  Subsumption          : 0.06
% 2.28/1.28  Abstraction          : 0.01
% 2.28/1.28  MUC search           : 0.00
% 2.28/1.28  Cooper               : 0.00
% 2.28/1.28  Total                : 0.53
% 2.28/1.28  Index Insertion      : 0.00
% 2.28/1.28  Index Deletion       : 0.00
% 2.28/1.28  Index Matching       : 0.00
% 2.28/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
