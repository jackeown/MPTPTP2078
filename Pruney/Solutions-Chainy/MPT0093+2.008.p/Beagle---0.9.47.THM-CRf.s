%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:32 EST 2020

% Result     : Theorem 10.62s
% Output     : CNFRefutation 10.72s
% Verified   : 
% Statistics : Number of formulae       :   41 (  57 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 103 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_30,plain,(
    ~ r1_tarski('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_59,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),A_27)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_27] : r1_tarski(A_27,A_27) ),
    inference(resolution,[status(thm)],[c_59,c_4])).

tff(c_34,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    ! [C_31,B_32,A_33] :
      ( r2_hidden(C_31,B_32)
      | ~ r2_hidden(C_31,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_40,B_41,B_42] :
      ( r2_hidden('#skF_1'(A_40,B_41),B_42)
      | ~ r1_tarski(A_40,B_42)
      | r1_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12067,plain,(
    ! [A_439,B_440,B_441,B_442] :
      ( r2_hidden('#skF_1'(A_439,B_440),B_441)
      | ~ r1_tarski(B_442,B_441)
      | ~ r1_tarski(A_439,B_442)
      | r1_tarski(A_439,B_440) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_12104,plain,(
    ! [A_443,B_444] :
      ( r2_hidden('#skF_1'(A_443,B_444),'#skF_5')
      | ~ r1_tarski(A_443,'#skF_4')
      | r1_tarski(A_443,B_444) ) ),
    inference(resolution,[status(thm)],[c_34,c_12067])).

tff(c_86,plain,(
    ! [D_34,A_35,B_36] :
      ( r2_hidden(D_34,k4_xboole_0(A_35,B_36))
      | r2_hidden(D_34,B_36)
      | ~ r2_hidden(D_34,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_104,plain,(
    ! [A_1,A_35,B_36] :
      ( r1_tarski(A_1,k4_xboole_0(A_35,B_36))
      | r2_hidden('#skF_1'(A_1,k4_xboole_0(A_35,B_36)),B_36)
      | ~ r2_hidden('#skF_1'(A_1,k4_xboole_0(A_35,B_36)),A_35) ) ),
    inference(resolution,[status(thm)],[c_86,c_4])).

tff(c_14414,plain,(
    ! [A_469,B_470] :
      ( r2_hidden('#skF_1'(A_469,k4_xboole_0('#skF_5',B_470)),B_470)
      | ~ r1_tarski(A_469,'#skF_4')
      | r1_tarski(A_469,k4_xboole_0('#skF_5',B_470)) ) ),
    inference(resolution,[status(thm)],[c_12104,c_104])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_36])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_187,plain,(
    ! [A_47,B_48,B_49] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_47,B_48),B_49),B_48)
      | r1_tarski(k4_xboole_0(A_47,B_48),B_49) ) ),
    inference(resolution,[status(thm)],[c_59,c_10])).

tff(c_198,plain,(
    ! [B_49] :
      ( ~ r2_hidden('#skF_1'('#skF_4',B_49),'#skF_6')
      | r1_tarski(k4_xboole_0('#skF_4','#skF_6'),B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_187])).

tff(c_201,plain,(
    ! [B_49] :
      ( ~ r2_hidden('#skF_1'('#skF_4',B_49),'#skF_6')
      | r1_tarski('#skF_4',B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_198])).

tff(c_14454,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | r1_tarski('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_14414,c_201])).

tff(c_14529,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_14454])).

tff(c_14531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_14529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.62/3.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.62/3.59  
% 10.62/3.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.62/3.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 10.62/3.60  
% 10.62/3.60  %Foreground sorts:
% 10.62/3.60  
% 10.62/3.60  
% 10.62/3.60  %Background operators:
% 10.62/3.60  
% 10.62/3.60  
% 10.62/3.60  %Foreground operators:
% 10.62/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.62/3.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.62/3.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.62/3.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.62/3.60  tff('#skF_5', type, '#skF_5': $i).
% 10.62/3.60  tff('#skF_6', type, '#skF_6': $i).
% 10.62/3.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.62/3.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.62/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.62/3.60  tff('#skF_4', type, '#skF_4': $i).
% 10.62/3.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.62/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.62/3.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.62/3.60  
% 10.72/3.61  tff(f_53, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 10.72/3.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.72/3.61  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.72/3.61  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.72/3.61  tff(c_30, plain, (~r1_tarski('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.72/3.61  tff(c_59, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), A_27) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.72/3.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.72/3.61  tff(c_77, plain, (![A_27]: (r1_tarski(A_27, A_27))), inference(resolution, [status(thm)], [c_59, c_4])).
% 10.72/3.61  tff(c_34, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.72/3.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.72/3.61  tff(c_82, plain, (![C_31, B_32, A_33]: (r2_hidden(C_31, B_32) | ~r2_hidden(C_31, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.72/3.61  tff(c_140, plain, (![A_40, B_41, B_42]: (r2_hidden('#skF_1'(A_40, B_41), B_42) | ~r1_tarski(A_40, B_42) | r1_tarski(A_40, B_41))), inference(resolution, [status(thm)], [c_6, c_82])).
% 10.72/3.61  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.72/3.61  tff(c_12067, plain, (![A_439, B_440, B_441, B_442]: (r2_hidden('#skF_1'(A_439, B_440), B_441) | ~r1_tarski(B_442, B_441) | ~r1_tarski(A_439, B_442) | r1_tarski(A_439, B_440))), inference(resolution, [status(thm)], [c_140, c_2])).
% 10.72/3.61  tff(c_12104, plain, (![A_443, B_444]: (r2_hidden('#skF_1'(A_443, B_444), '#skF_5') | ~r1_tarski(A_443, '#skF_4') | r1_tarski(A_443, B_444))), inference(resolution, [status(thm)], [c_34, c_12067])).
% 10.72/3.61  tff(c_86, plain, (![D_34, A_35, B_36]: (r2_hidden(D_34, k4_xboole_0(A_35, B_36)) | r2_hidden(D_34, B_36) | ~r2_hidden(D_34, A_35))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.72/3.61  tff(c_104, plain, (![A_1, A_35, B_36]: (r1_tarski(A_1, k4_xboole_0(A_35, B_36)) | r2_hidden('#skF_1'(A_1, k4_xboole_0(A_35, B_36)), B_36) | ~r2_hidden('#skF_1'(A_1, k4_xboole_0(A_35, B_36)), A_35))), inference(resolution, [status(thm)], [c_86, c_4])).
% 10.72/3.61  tff(c_14414, plain, (![A_469, B_470]: (r2_hidden('#skF_1'(A_469, k4_xboole_0('#skF_5', B_470)), B_470) | ~r1_tarski(A_469, '#skF_4') | r1_tarski(A_469, k4_xboole_0('#skF_5', B_470)))), inference(resolution, [status(thm)], [c_12104, c_104])).
% 10.72/3.61  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.72/3.61  tff(c_36, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.72/3.61  tff(c_44, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_36])).
% 10.72/3.61  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.72/3.61  tff(c_187, plain, (![A_47, B_48, B_49]: (~r2_hidden('#skF_1'(k4_xboole_0(A_47, B_48), B_49), B_48) | r1_tarski(k4_xboole_0(A_47, B_48), B_49))), inference(resolution, [status(thm)], [c_59, c_10])).
% 10.72/3.61  tff(c_198, plain, (![B_49]: (~r2_hidden('#skF_1'('#skF_4', B_49), '#skF_6') | r1_tarski(k4_xboole_0('#skF_4', '#skF_6'), B_49))), inference(superposition, [status(thm), theory('equality')], [c_44, c_187])).
% 10.72/3.61  tff(c_201, plain, (![B_49]: (~r2_hidden('#skF_1'('#skF_4', B_49), '#skF_6') | r1_tarski('#skF_4', B_49))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_198])).
% 10.72/3.61  tff(c_14454, plain, (~r1_tarski('#skF_4', '#skF_4') | r1_tarski('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_14414, c_201])).
% 10.72/3.61  tff(c_14529, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_14454])).
% 10.72/3.61  tff(c_14531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_14529])).
% 10.72/3.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.72/3.61  
% 10.72/3.61  Inference rules
% 10.72/3.61  ----------------------
% 10.72/3.61  #Ref     : 0
% 10.72/3.61  #Sup     : 3871
% 10.72/3.61  #Fact    : 0
% 10.72/3.61  #Define  : 0
% 10.72/3.61  #Split   : 5
% 10.72/3.61  #Chain   : 0
% 10.72/3.61  #Close   : 0
% 10.72/3.61  
% 10.72/3.61  Ordering : KBO
% 10.72/3.61  
% 10.72/3.61  Simplification rules
% 10.72/3.61  ----------------------
% 10.72/3.61  #Subsume      : 1643
% 10.72/3.61  #Demod        : 1962
% 10.72/3.61  #Tautology    : 906
% 10.72/3.61  #SimpNegUnit  : 56
% 10.72/3.61  #BackRed      : 3
% 10.72/3.61  
% 10.72/3.61  #Partial instantiations: 0
% 10.72/3.61  #Strategies tried      : 1
% 10.72/3.61  
% 10.72/3.61  Timing (in seconds)
% 10.72/3.61  ----------------------
% 10.72/3.61  Preprocessing        : 0.30
% 10.72/3.61  Parsing              : 0.15
% 10.72/3.61  CNF conversion       : 0.03
% 10.72/3.61  Main loop            : 2.48
% 10.72/3.61  Inferencing          : 0.66
% 10.72/3.61  Reduction            : 0.96
% 10.72/3.61  Demodulation         : 0.75
% 10.72/3.61  BG Simplification    : 0.07
% 10.72/3.61  Subsumption          : 0.68
% 10.72/3.61  Abstraction          : 0.11
% 10.72/3.61  MUC search           : 0.00
% 10.72/3.61  Cooper               : 0.00
% 10.72/3.61  Total                : 2.81
% 10.72/3.61  Index Insertion      : 0.00
% 10.72/3.61  Index Deletion       : 0.00
% 10.72/3.61  Index Matching       : 0.00
% 10.72/3.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
