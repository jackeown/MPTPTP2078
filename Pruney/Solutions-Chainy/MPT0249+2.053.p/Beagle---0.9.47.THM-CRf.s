%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:30 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   47 (  91 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 161 expanded)
%              Number of equality atoms :   24 (  77 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_111,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40),B_40)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_129,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(k2_xboole_0(A_42,B_44),C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_141,plain,(
    ! [A_45,B_46] : r1_tarski(A_45,k2_xboole_0(A_45,B_46)) ),
    inference(resolution,[status(thm)],[c_124,c_129])).

tff(c_151,plain,(
    r1_tarski('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_141])).

tff(c_373,plain,(
    ! [B_73,A_74] :
      ( k1_tarski(B_73) = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_tarski(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_376,plain,
    ( k1_tarski('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_151,c_373])).

tff(c_386,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_376])).

tff(c_102,plain,(
    ! [D_33,B_34,A_35] :
      ( ~ r2_hidden(D_33,B_34)
      | r2_hidden(D_33,k2_xboole_0(A_35,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_108,plain,(
    ! [D_33] :
      ( ~ r2_hidden(D_33,'#skF_6')
      | r2_hidden(D_33,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_102])).

tff(c_494,plain,(
    ! [D_78] :
      ( ~ r2_hidden(D_78,'#skF_6')
      | r2_hidden(D_78,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_108])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_598,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_86,'#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_494,c_4])).

tff(c_603,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_598])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( k1_tarski(B_22) = A_21
      | k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_tarski(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_412,plain,(
    ! [A_21] :
      ( k1_tarski('#skF_4') = A_21
      | k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_34])).

tff(c_435,plain,(
    ! [A_21] :
      ( A_21 = '#skF_5'
      | k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_412])).

tff(c_627,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_603,c_435])).

tff(c_631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_46,c_627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.38  
% 2.54/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.39  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.54/1.39  
% 2.54/1.39  %Foreground sorts:
% 2.54/1.39  
% 2.54/1.39  
% 2.54/1.39  %Background operators:
% 2.54/1.39  
% 2.54/1.39  
% 2.54/1.39  %Foreground operators:
% 2.54/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.54/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.54/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.54/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.39  
% 2.80/1.40  tff(f_72, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.80/1.40  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.80/1.40  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.80/1.40  tff(f_57, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.80/1.40  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.80/1.40  tff(c_42, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.80/1.40  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.80/1.40  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.40  tff(c_44, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.80/1.40  tff(c_48, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.80/1.40  tff(c_111, plain, (![A_39, B_40]: (~r2_hidden('#skF_1'(A_39, B_40), B_40) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.40  tff(c_124, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_111])).
% 2.80/1.40  tff(c_129, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(k2_xboole_0(A_42, B_44), C_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.80/1.40  tff(c_141, plain, (![A_45, B_46]: (r1_tarski(A_45, k2_xboole_0(A_45, B_46)))), inference(resolution, [status(thm)], [c_124, c_129])).
% 2.80/1.40  tff(c_151, plain, (r1_tarski('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_141])).
% 2.80/1.40  tff(c_373, plain, (![B_73, A_74]: (k1_tarski(B_73)=A_74 | k1_xboole_0=A_74 | ~r1_tarski(A_74, k1_tarski(B_73)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.40  tff(c_376, plain, (k1_tarski('#skF_4')='#skF_5' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_151, c_373])).
% 2.80/1.40  tff(c_386, plain, (k1_tarski('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_44, c_376])).
% 2.80/1.40  tff(c_102, plain, (![D_33, B_34, A_35]: (~r2_hidden(D_33, B_34) | r2_hidden(D_33, k2_xboole_0(A_35, B_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.40  tff(c_108, plain, (![D_33]: (~r2_hidden(D_33, '#skF_6') | r2_hidden(D_33, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_102])).
% 2.80/1.40  tff(c_494, plain, (![D_78]: (~r2_hidden(D_78, '#skF_6') | r2_hidden(D_78, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_108])).
% 2.80/1.40  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.40  tff(c_598, plain, (![A_86]: (r1_tarski(A_86, '#skF_5') | ~r2_hidden('#skF_1'(A_86, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_494, c_4])).
% 2.80/1.40  tff(c_603, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_598])).
% 2.80/1.40  tff(c_34, plain, (![B_22, A_21]: (k1_tarski(B_22)=A_21 | k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_tarski(B_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.40  tff(c_412, plain, (![A_21]: (k1_tarski('#skF_4')=A_21 | k1_xboole_0=A_21 | ~r1_tarski(A_21, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_386, c_34])).
% 2.80/1.40  tff(c_435, plain, (![A_21]: (A_21='#skF_5' | k1_xboole_0=A_21 | ~r1_tarski(A_21, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_412])).
% 2.80/1.40  tff(c_627, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_603, c_435])).
% 2.80/1.40  tff(c_631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_46, c_627])).
% 2.80/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.40  
% 2.80/1.40  Inference rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Ref     : 0
% 2.80/1.40  #Sup     : 128
% 2.80/1.40  #Fact    : 0
% 2.80/1.40  #Define  : 0
% 2.80/1.40  #Split   : 0
% 2.80/1.40  #Chain   : 0
% 2.80/1.40  #Close   : 0
% 2.80/1.40  
% 2.80/1.40  Ordering : KBO
% 2.80/1.40  
% 2.80/1.40  Simplification rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Subsume      : 7
% 2.80/1.40  #Demod        : 50
% 2.80/1.40  #Tautology    : 65
% 2.80/1.40  #SimpNegUnit  : 4
% 2.80/1.40  #BackRed      : 9
% 2.80/1.40  
% 2.80/1.40  #Partial instantiations: 0
% 2.80/1.40  #Strategies tried      : 1
% 2.80/1.40  
% 2.80/1.40  Timing (in seconds)
% 2.80/1.40  ----------------------
% 2.80/1.40  Preprocessing        : 0.32
% 2.80/1.40  Parsing              : 0.16
% 2.80/1.40  CNF conversion       : 0.02
% 2.80/1.40  Main loop            : 0.33
% 2.80/1.40  Inferencing          : 0.12
% 2.80/1.40  Reduction            : 0.11
% 2.80/1.40  Demodulation         : 0.08
% 2.80/1.40  BG Simplification    : 0.02
% 2.80/1.40  Subsumption          : 0.06
% 2.80/1.40  Abstraction          : 0.01
% 2.80/1.40  MUC search           : 0.00
% 2.80/1.40  Cooper               : 0.00
% 2.80/1.40  Total                : 0.67
% 2.80/1.40  Index Insertion      : 0.00
% 2.80/1.40  Index Deletion       : 0.00
% 2.80/1.40  Index Matching       : 0.00
% 2.80/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
