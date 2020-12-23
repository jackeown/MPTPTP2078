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
% DateTime   : Thu Dec  3 09:57:12 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 103 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( ! [C] :
            ( r2_hidden(C,A)
           => r1_tarski(B,C) )
       => ( A = k1_xboole_0
          | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_51,axiom,(
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

tff(c_42,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),A_30)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    ! [A_30] : r1_tarski(A_30,A_30) ),
    inference(resolution,[status(thm)],[c_42,c_4])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92,plain,(
    ! [A_47,C_48] :
      ( r2_hidden('#skF_2'(A_47,k1_setfam_1(A_47),C_48),A_47)
      | r2_hidden(C_48,k1_setfam_1(A_47))
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ! [C_26] :
      ( r1_tarski('#skF_7',C_26)
      | ~ r2_hidden(C_26,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_100,plain,(
    ! [C_48] :
      ( r1_tarski('#skF_7','#skF_2'('#skF_6',k1_setfam_1('#skF_6'),C_48))
      | r2_hidden(C_48,k1_setfam_1('#skF_6'))
      | k1_xboole_0 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_92,c_34])).

tff(c_108,plain,(
    ! [C_48] :
      ( r1_tarski('#skF_7','#skF_2'('#skF_6',k1_setfam_1('#skF_6'),C_48))
      | r2_hidden(C_48,k1_setfam_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_100])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    ! [C_34,B_35,A_36] :
      ( r2_hidden(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [A_40,B_41,B_42] :
      ( r2_hidden('#skF_1'(A_40,B_41),B_42)
      | ~ r1_tarski(A_40,B_42)
      | r1_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [A_55,B_56,B_57,B_58] :
      ( r2_hidden('#skF_1'(A_55,B_56),B_57)
      | ~ r1_tarski(B_58,B_57)
      | ~ r1_tarski(A_55,B_58)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_779,plain,(
    ! [A_144,B_145,C_146] :
      ( r2_hidden('#skF_1'(A_144,B_145),'#skF_2'('#skF_6',k1_setfam_1('#skF_6'),C_146))
      | ~ r1_tarski(A_144,'#skF_7')
      | r1_tarski(A_144,B_145)
      | r2_hidden(C_146,k1_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_108,c_129])).

tff(c_22,plain,(
    ! [C_18,A_6] :
      ( ~ r2_hidden(C_18,'#skF_2'(A_6,k1_setfam_1(A_6),C_18))
      | r2_hidden(C_18,k1_setfam_1(A_6))
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_783,plain,(
    ! [A_144,B_145] :
      ( k1_xboole_0 = '#skF_6'
      | ~ r1_tarski(A_144,'#skF_7')
      | r1_tarski(A_144,B_145)
      | r2_hidden('#skF_1'(A_144,B_145),k1_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_779,c_22])).

tff(c_798,plain,(
    ! [A_147,B_148] :
      ( ~ r1_tarski(A_147,'#skF_7')
      | r1_tarski(A_147,B_148)
      | r2_hidden('#skF_1'(A_147,B_148),k1_setfam_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_783])).

tff(c_913,plain,(
    ! [A_153] :
      ( ~ r1_tarski(A_153,'#skF_7')
      | r1_tarski(A_153,k1_setfam_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_798,c_4])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_7',k1_setfam_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_924,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_913,c_30])).

tff(c_933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_924])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.66  
% 3.43/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.66  %$ r2_hidden > r1_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.43/1.66  
% 3.43/1.66  %Foreground sorts:
% 3.43/1.66  
% 3.43/1.66  
% 3.43/1.66  %Background operators:
% 3.43/1.66  
% 3.43/1.66  
% 3.43/1.66  %Foreground operators:
% 3.43/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.43/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.43/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.43/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.43/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.43/1.66  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.43/1.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.43/1.66  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.43/1.66  
% 3.43/1.67  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.43/1.67  tff(f_61, negated_conjecture, ~(![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 3.43/1.67  tff(f_51, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 3.43/1.67  tff(c_42, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), A_30) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.43/1.67  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.43/1.67  tff(c_51, plain, (![A_30]: (r1_tarski(A_30, A_30))), inference(resolution, [status(thm)], [c_42, c_4])).
% 3.43/1.67  tff(c_32, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.43/1.67  tff(c_92, plain, (![A_47, C_48]: (r2_hidden('#skF_2'(A_47, k1_setfam_1(A_47), C_48), A_47) | r2_hidden(C_48, k1_setfam_1(A_47)) | k1_xboole_0=A_47)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.43/1.67  tff(c_34, plain, (![C_26]: (r1_tarski('#skF_7', C_26) | ~r2_hidden(C_26, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.43/1.67  tff(c_100, plain, (![C_48]: (r1_tarski('#skF_7', '#skF_2'('#skF_6', k1_setfam_1('#skF_6'), C_48)) | r2_hidden(C_48, k1_setfam_1('#skF_6')) | k1_xboole_0='#skF_6')), inference(resolution, [status(thm)], [c_92, c_34])).
% 3.43/1.67  tff(c_108, plain, (![C_48]: (r1_tarski('#skF_7', '#skF_2'('#skF_6', k1_setfam_1('#skF_6'), C_48)) | r2_hidden(C_48, k1_setfam_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_32, c_100])).
% 3.43/1.67  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.43/1.67  tff(c_55, plain, (![C_34, B_35, A_36]: (r2_hidden(C_34, B_35) | ~r2_hidden(C_34, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.43/1.67  tff(c_63, plain, (![A_40, B_41, B_42]: (r2_hidden('#skF_1'(A_40, B_41), B_42) | ~r1_tarski(A_40, B_42) | r1_tarski(A_40, B_41))), inference(resolution, [status(thm)], [c_6, c_55])).
% 3.43/1.67  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.43/1.67  tff(c_129, plain, (![A_55, B_56, B_57, B_58]: (r2_hidden('#skF_1'(A_55, B_56), B_57) | ~r1_tarski(B_58, B_57) | ~r1_tarski(A_55, B_58) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_63, c_2])).
% 3.43/1.67  tff(c_779, plain, (![A_144, B_145, C_146]: (r2_hidden('#skF_1'(A_144, B_145), '#skF_2'('#skF_6', k1_setfam_1('#skF_6'), C_146)) | ~r1_tarski(A_144, '#skF_7') | r1_tarski(A_144, B_145) | r2_hidden(C_146, k1_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_108, c_129])).
% 3.43/1.67  tff(c_22, plain, (![C_18, A_6]: (~r2_hidden(C_18, '#skF_2'(A_6, k1_setfam_1(A_6), C_18)) | r2_hidden(C_18, k1_setfam_1(A_6)) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.43/1.67  tff(c_783, plain, (![A_144, B_145]: (k1_xboole_0='#skF_6' | ~r1_tarski(A_144, '#skF_7') | r1_tarski(A_144, B_145) | r2_hidden('#skF_1'(A_144, B_145), k1_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_779, c_22])).
% 3.43/1.67  tff(c_798, plain, (![A_147, B_148]: (~r1_tarski(A_147, '#skF_7') | r1_tarski(A_147, B_148) | r2_hidden('#skF_1'(A_147, B_148), k1_setfam_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_32, c_783])).
% 3.43/1.67  tff(c_913, plain, (![A_153]: (~r1_tarski(A_153, '#skF_7') | r1_tarski(A_153, k1_setfam_1('#skF_6')))), inference(resolution, [status(thm)], [c_798, c_4])).
% 3.43/1.67  tff(c_30, plain, (~r1_tarski('#skF_7', k1_setfam_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.43/1.67  tff(c_924, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_913, c_30])).
% 3.43/1.67  tff(c_933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_924])).
% 3.43/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.67  
% 3.43/1.67  Inference rules
% 3.43/1.67  ----------------------
% 3.43/1.67  #Ref     : 0
% 3.43/1.67  #Sup     : 218
% 3.43/1.67  #Fact    : 0
% 3.43/1.67  #Define  : 0
% 3.43/1.67  #Split   : 1
% 3.43/1.67  #Chain   : 0
% 3.43/1.67  #Close   : 0
% 3.43/1.67  
% 3.43/1.67  Ordering : KBO
% 3.43/1.67  
% 3.43/1.67  Simplification rules
% 3.43/1.67  ----------------------
% 3.43/1.67  #Subsume      : 15
% 3.43/1.67  #Demod        : 10
% 3.43/1.67  #Tautology    : 17
% 3.43/1.67  #SimpNegUnit  : 9
% 3.43/1.67  #BackRed      : 0
% 3.43/1.67  
% 3.43/1.67  #Partial instantiations: 0
% 3.43/1.67  #Strategies tried      : 1
% 3.43/1.67  
% 3.43/1.67  Timing (in seconds)
% 3.43/1.67  ----------------------
% 3.43/1.67  Preprocessing        : 0.35
% 3.43/1.67  Parsing              : 0.18
% 3.43/1.67  CNF conversion       : 0.03
% 3.43/1.67  Main loop            : 0.50
% 3.43/1.67  Inferencing          : 0.18
% 3.43/1.67  Reduction            : 0.10
% 3.43/1.67  Demodulation         : 0.06
% 3.43/1.67  BG Simplification    : 0.03
% 3.43/1.67  Subsumption          : 0.15
% 3.43/1.67  Abstraction          : 0.03
% 3.43/1.67  MUC search           : 0.00
% 3.43/1.67  Cooper               : 0.00
% 3.43/1.67  Total                : 0.87
% 3.43/1.67  Index Insertion      : 0.00
% 3.43/1.67  Index Deletion       : 0.00
% 3.43/1.67  Index Matching       : 0.00
% 3.43/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
