%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:10 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  99 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
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

tff(f_81,axiom,(
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

tff(f_62,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_50,axiom,(
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

tff(c_40,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_38] : r1_tarski(A_38,A_38) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_42,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_135,plain,(
    ! [C_54,D_55,A_56] :
      ( r2_hidden(C_54,D_55)
      | ~ r2_hidden(D_55,A_56)
      | ~ r2_hidden(C_54,k1_setfam_1(A_56))
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_150,plain,(
    ! [C_54] :
      ( r2_hidden(C_54,'#skF_7')
      | ~ r2_hidden(C_54,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_42,c_135])).

tff(c_151,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_106,plain,(
    ! [C_48,B_49,A_50] :
      ( r2_hidden(C_48,B_49)
      | ~ r2_hidden(C_48,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_7',B_51)
      | ~ r1_tarski('#skF_8',B_51) ) ),
    inference(resolution,[status(thm)],[c_42,c_106])).

tff(c_14,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_63,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,B_41)
      | ~ r2_hidden(C_42,A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,(
    ! [C_42] : ~ r2_hidden(C_42,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_63])).

tff(c_127,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_119,c_66])).

tff(c_153,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_127])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_153])).

tff(c_165,plain,(
    ! [C_57] :
      ( r2_hidden(C_57,'#skF_7')
      | ~ r2_hidden(C_57,k1_setfam_1('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_237,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_8'),B_64),'#skF_7')
      | r1_tarski(k1_setfam_1('#skF_8'),B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_165])).

tff(c_245,plain,(
    r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_237,c_4])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.06/1.31  
% 2.06/1.31  %Foreground sorts:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Background operators:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Foreground operators:
% 2.06/1.31  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.06/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.06/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.06/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.06/1.31  
% 2.06/1.32  tff(f_86, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.06/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.06/1.32  tff(f_81, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.06/1.32  tff(f_62, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.06/1.32  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.06/1.32  tff(c_40, plain, (~r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.06/1.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.32  tff(c_57, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.32  tff(c_62, plain, (![A_38]: (r1_tarski(A_38, A_38))), inference(resolution, [status(thm)], [c_57, c_4])).
% 2.06/1.32  tff(c_42, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.06/1.32  tff(c_135, plain, (![C_54, D_55, A_56]: (r2_hidden(C_54, D_55) | ~r2_hidden(D_55, A_56) | ~r2_hidden(C_54, k1_setfam_1(A_56)) | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.06/1.32  tff(c_150, plain, (![C_54]: (r2_hidden(C_54, '#skF_7') | ~r2_hidden(C_54, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_42, c_135])).
% 2.06/1.32  tff(c_151, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_150])).
% 2.06/1.32  tff(c_106, plain, (![C_48, B_49, A_50]: (r2_hidden(C_48, B_49) | ~r2_hidden(C_48, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.32  tff(c_119, plain, (![B_51]: (r2_hidden('#skF_7', B_51) | ~r1_tarski('#skF_8', B_51))), inference(resolution, [status(thm)], [c_42, c_106])).
% 2.06/1.32  tff(c_14, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.32  tff(c_63, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, B_41) | ~r2_hidden(C_42, A_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.32  tff(c_66, plain, (![C_42]: (~r2_hidden(C_42, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_63])).
% 2.06/1.32  tff(c_127, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_119, c_66])).
% 2.06/1.32  tff(c_153, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_127])).
% 2.06/1.32  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_153])).
% 2.06/1.32  tff(c_165, plain, (![C_57]: (r2_hidden(C_57, '#skF_7') | ~r2_hidden(C_57, k1_setfam_1('#skF_8')))), inference(splitRight, [status(thm)], [c_150])).
% 2.06/1.32  tff(c_237, plain, (![B_64]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_8'), B_64), '#skF_7') | r1_tarski(k1_setfam_1('#skF_8'), B_64))), inference(resolution, [status(thm)], [c_6, c_165])).
% 2.06/1.32  tff(c_245, plain, (r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_237, c_4])).
% 2.06/1.32  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_245])).
% 2.06/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.32  
% 2.06/1.32  Inference rules
% 2.06/1.32  ----------------------
% 2.06/1.32  #Ref     : 0
% 2.06/1.32  #Sup     : 43
% 2.06/1.32  #Fact    : 0
% 2.06/1.32  #Define  : 0
% 2.06/1.32  #Split   : 2
% 2.06/1.32  #Chain   : 0
% 2.06/1.32  #Close   : 0
% 2.06/1.32  
% 2.06/1.32  Ordering : KBO
% 2.06/1.32  
% 2.06/1.32  Simplification rules
% 2.06/1.32  ----------------------
% 2.06/1.32  #Subsume      : 5
% 2.06/1.32  #Demod        : 13
% 2.06/1.32  #Tautology    : 8
% 2.06/1.32  #SimpNegUnit  : 2
% 2.06/1.32  #BackRed      : 8
% 2.06/1.32  
% 2.06/1.32  #Partial instantiations: 0
% 2.06/1.32  #Strategies tried      : 1
% 2.06/1.32  
% 2.06/1.32  Timing (in seconds)
% 2.06/1.32  ----------------------
% 2.06/1.32  Preprocessing        : 0.30
% 2.06/1.33  Parsing              : 0.16
% 2.06/1.33  CNF conversion       : 0.02
% 2.33/1.33  Main loop            : 0.22
% 2.33/1.33  Inferencing          : 0.07
% 2.33/1.33  Reduction            : 0.06
% 2.33/1.33  Demodulation         : 0.04
% 2.33/1.33  BG Simplification    : 0.02
% 2.33/1.33  Subsumption          : 0.06
% 2.33/1.33  Abstraction          : 0.01
% 2.33/1.33  MUC search           : 0.00
% 2.33/1.33  Cooper               : 0.00
% 2.33/1.33  Total                : 0.54
% 2.33/1.33  Index Insertion      : 0.00
% 2.33/1.33  Index Deletion       : 0.00
% 2.33/1.33  Index Matching       : 0.00
% 2.33/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
