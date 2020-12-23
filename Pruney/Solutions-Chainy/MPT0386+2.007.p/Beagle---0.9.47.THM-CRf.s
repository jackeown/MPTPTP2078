%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:09 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   45 (  67 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 ( 100 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(c_56,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_247,plain,(
    ! [C_63,B_64,A_65] :
      ( r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_254,plain,(
    ! [B_66] :
      ( r2_hidden('#skF_8',B_66)
      | ~ r1_tarski('#skF_9',B_66) ) ),
    inference(resolution,[status(thm)],[c_58,c_247])).

tff(c_96,plain,(
    ! [D_44,B_45,A_46] :
      ( ~ r2_hidden(D_44,B_45)
      | ~ r2_hidden(D_44,k4_xboole_0(A_46,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    ! [D_44,A_16] :
      ( ~ r2_hidden(D_44,k1_xboole_0)
      | ~ r2_hidden(D_44,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_96])).

tff(c_274,plain,(
    ! [A_16] :
      ( ~ r2_hidden('#skF_8',A_16)
      | ~ r1_tarski('#skF_9',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_254,c_99])).

tff(c_276,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_308,plain,(
    k4_xboole_0('#skF_9',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_276])).

tff(c_310,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_308])).

tff(c_380,plain,(
    ! [C_78,D_79,A_80] :
      ( r2_hidden(C_78,D_79)
      | ~ r2_hidden(D_79,A_80)
      | ~ r2_hidden(C_78,k1_setfam_1(A_80))
      | k1_xboole_0 = A_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_388,plain,(
    ! [C_78] :
      ( r2_hidden(C_78,'#skF_8')
      | ~ r2_hidden(C_78,k1_setfam_1('#skF_9'))
      | k1_xboole_0 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_58,c_380])).

tff(c_395,plain,(
    ! [C_81] :
      ( r2_hidden(C_81,'#skF_8')
      | ~ r2_hidden(C_81,k1_setfam_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_310,c_388])).

tff(c_484,plain,(
    ! [B_87] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_9'),B_87),'#skF_8')
      | r1_tarski(k1_setfam_1('#skF_9'),B_87) ) ),
    inference(resolution,[status(thm)],[c_6,c_395])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_492,plain,(
    r1_tarski(k1_setfam_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_484,c_4])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_492])).

tff(c_499,plain,(
    ! [A_16] : ~ r2_hidden('#skF_8',A_16) ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 11:07:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.35  
% 2.38/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.35  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5
% 2.38/1.35  
% 2.38/1.35  %Foreground sorts:
% 2.38/1.35  
% 2.38/1.35  
% 2.38/1.35  %Background operators:
% 2.38/1.35  
% 2.38/1.35  
% 2.38/1.35  %Foreground operators:
% 2.38/1.35  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.38/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.38/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.35  tff('#skF_9', type, '#skF_9': $i).
% 2.38/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.38/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.35  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.38/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.35  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.38/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.38/1.35  
% 2.38/1.37  tff(f_74, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.38/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.38/1.37  tff(f_50, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.38/1.37  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.38/1.37  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.38/1.37  tff(f_69, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.38/1.37  tff(c_56, plain, (~r1_tarski(k1_setfam_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.38/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.37  tff(c_32, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.38/1.37  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.37  tff(c_58, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.38/1.37  tff(c_247, plain, (![C_63, B_64, A_65]: (r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.37  tff(c_254, plain, (![B_66]: (r2_hidden('#skF_8', B_66) | ~r1_tarski('#skF_9', B_66))), inference(resolution, [status(thm)], [c_58, c_247])).
% 2.38/1.37  tff(c_96, plain, (![D_44, B_45, A_46]: (~r2_hidden(D_44, B_45) | ~r2_hidden(D_44, k4_xboole_0(A_46, B_45)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.38/1.37  tff(c_99, plain, (![D_44, A_16]: (~r2_hidden(D_44, k1_xboole_0) | ~r2_hidden(D_44, A_16))), inference(superposition, [status(thm), theory('equality')], [c_32, c_96])).
% 2.38/1.37  tff(c_274, plain, (![A_16]: (~r2_hidden('#skF_8', A_16) | ~r1_tarski('#skF_9', k1_xboole_0))), inference(resolution, [status(thm)], [c_254, c_99])).
% 2.38/1.37  tff(c_276, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_274])).
% 2.38/1.37  tff(c_308, plain, (k4_xboole_0('#skF_9', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_276])).
% 2.38/1.37  tff(c_310, plain, (k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_308])).
% 2.38/1.37  tff(c_380, plain, (![C_78, D_79, A_80]: (r2_hidden(C_78, D_79) | ~r2_hidden(D_79, A_80) | ~r2_hidden(C_78, k1_setfam_1(A_80)) | k1_xboole_0=A_80)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.38/1.37  tff(c_388, plain, (![C_78]: (r2_hidden(C_78, '#skF_8') | ~r2_hidden(C_78, k1_setfam_1('#skF_9')) | k1_xboole_0='#skF_9')), inference(resolution, [status(thm)], [c_58, c_380])).
% 2.38/1.37  tff(c_395, plain, (![C_81]: (r2_hidden(C_81, '#skF_8') | ~r2_hidden(C_81, k1_setfam_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_310, c_388])).
% 2.38/1.37  tff(c_484, plain, (![B_87]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_9'), B_87), '#skF_8') | r1_tarski(k1_setfam_1('#skF_9'), B_87))), inference(resolution, [status(thm)], [c_6, c_395])).
% 2.38/1.37  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.37  tff(c_492, plain, (r1_tarski(k1_setfam_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_484, c_4])).
% 2.38/1.37  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_492])).
% 2.38/1.37  tff(c_499, plain, (![A_16]: (~r2_hidden('#skF_8', A_16))), inference(splitRight, [status(thm)], [c_274])).
% 2.38/1.37  tff(c_503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_499, c_58])).
% 2.38/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.37  
% 2.38/1.37  Inference rules
% 2.38/1.37  ----------------------
% 2.38/1.37  #Ref     : 0
% 2.38/1.37  #Sup     : 106
% 2.38/1.37  #Fact    : 0
% 2.38/1.37  #Define  : 0
% 2.38/1.37  #Split   : 3
% 2.38/1.37  #Chain   : 0
% 2.38/1.37  #Close   : 0
% 2.38/1.37  
% 2.38/1.37  Ordering : KBO
% 2.38/1.37  
% 2.38/1.37  Simplification rules
% 2.38/1.37  ----------------------
% 2.38/1.37  #Subsume      : 32
% 2.38/1.37  #Demod        : 23
% 2.38/1.37  #Tautology    : 36
% 2.38/1.37  #SimpNegUnit  : 6
% 2.38/1.37  #BackRed      : 2
% 2.38/1.37  
% 2.38/1.37  #Partial instantiations: 0
% 2.38/1.37  #Strategies tried      : 1
% 2.38/1.37  
% 2.38/1.37  Timing (in seconds)
% 2.38/1.37  ----------------------
% 2.38/1.37  Preprocessing        : 0.28
% 2.38/1.37  Parsing              : 0.14
% 2.38/1.37  CNF conversion       : 0.03
% 2.38/1.37  Main loop            : 0.27
% 2.38/1.37  Inferencing          : 0.09
% 2.38/1.37  Reduction            : 0.08
% 2.38/1.37  Demodulation         : 0.05
% 2.38/1.37  BG Simplification    : 0.02
% 2.38/1.37  Subsumption          : 0.07
% 2.38/1.37  Abstraction          : 0.01
% 2.38/1.37  MUC search           : 0.00
% 2.38/1.37  Cooper               : 0.00
% 2.38/1.37  Total                : 0.58
% 2.38/1.37  Index Insertion      : 0.00
% 2.38/1.37  Index Deletion       : 0.00
% 2.38/1.37  Index Matching       : 0.00
% 2.38/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
