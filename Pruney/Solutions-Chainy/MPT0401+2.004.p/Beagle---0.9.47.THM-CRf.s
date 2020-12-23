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
% DateTime   : Thu Dec  3 09:57:38 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   29 (  34 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  48 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    r1_setfam_1('#skF_6',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_43,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden('#skF_4'(A_31,B_32,C_33),B_32)
      | ~ r2_hidden(C_33,A_31)
      | ~ r1_setfam_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    ! [A_43,A_44,C_45] :
      ( '#skF_4'(A_43,k1_tarski(A_44),C_45) = A_44
      | ~ r2_hidden(C_45,A_43)
      | ~ r1_setfam_1(A_43,k1_tarski(A_44)) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_99,plain,(
    ! [C_48] :
      ( '#skF_4'('#skF_6',k1_tarski('#skF_5'),C_48) = '#skF_5'
      | ~ r2_hidden(C_48,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_14,plain,(
    ! [C_16,A_6,B_7] :
      ( r1_tarski(C_16,'#skF_4'(A_6,B_7,C_16))
      | ~ r2_hidden(C_16,A_6)
      | ~ r1_setfam_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_105,plain,(
    ! [C_48] :
      ( r1_tarski(C_48,'#skF_5')
      | ~ r2_hidden(C_48,'#skF_6')
      | ~ r1_setfam_1('#skF_6',k1_tarski('#skF_5'))
      | ~ r2_hidden(C_48,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_14])).

tff(c_118,plain,(
    ! [C_49] :
      ( r1_tarski(C_49,'#skF_5')
      | ~ r2_hidden(C_49,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_105])).

tff(c_137,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_118])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:58:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.21  
% 1.84/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.21  %$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 1.84/1.21  
% 1.84/1.21  %Foreground sorts:
% 1.84/1.21  
% 1.84/1.21  
% 1.84/1.21  %Background operators:
% 1.84/1.21  
% 1.84/1.21  
% 1.84/1.21  %Foreground operators:
% 1.84/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.21  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.84/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.84/1.21  tff('#skF_7', type, '#skF_7': $i).
% 1.84/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.84/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.84/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.84/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.84/1.21  
% 1.84/1.22  tff(f_52, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_setfam_1)).
% 1.84/1.22  tff(f_44, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.84/1.22  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.84/1.22  tff(c_22, plain, (~r1_tarski('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.84/1.22  tff(c_24, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.84/1.22  tff(c_26, plain, (r1_setfam_1('#skF_6', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.84/1.22  tff(c_43, plain, (![A_31, B_32, C_33]: (r2_hidden('#skF_4'(A_31, B_32, C_33), B_32) | ~r2_hidden(C_33, A_31) | ~r1_setfam_1(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.22  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.84/1.22  tff(c_68, plain, (![A_43, A_44, C_45]: ('#skF_4'(A_43, k1_tarski(A_44), C_45)=A_44 | ~r2_hidden(C_45, A_43) | ~r1_setfam_1(A_43, k1_tarski(A_44)))), inference(resolution, [status(thm)], [c_43, c_2])).
% 1.84/1.22  tff(c_99, plain, (![C_48]: ('#skF_4'('#skF_6', k1_tarski('#skF_5'), C_48)='#skF_5' | ~r2_hidden(C_48, '#skF_6'))), inference(resolution, [status(thm)], [c_26, c_68])).
% 1.84/1.22  tff(c_14, plain, (![C_16, A_6, B_7]: (r1_tarski(C_16, '#skF_4'(A_6, B_7, C_16)) | ~r2_hidden(C_16, A_6) | ~r1_setfam_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.22  tff(c_105, plain, (![C_48]: (r1_tarski(C_48, '#skF_5') | ~r2_hidden(C_48, '#skF_6') | ~r1_setfam_1('#skF_6', k1_tarski('#skF_5')) | ~r2_hidden(C_48, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_14])).
% 1.84/1.22  tff(c_118, plain, (![C_49]: (r1_tarski(C_49, '#skF_5') | ~r2_hidden(C_49, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_105])).
% 1.84/1.22  tff(c_137, plain, (r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_118])).
% 1.84/1.22  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_137])).
% 1.84/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.22  
% 1.84/1.22  Inference rules
% 1.84/1.22  ----------------------
% 1.84/1.22  #Ref     : 0
% 1.84/1.22  #Sup     : 22
% 1.84/1.22  #Fact    : 0
% 1.84/1.22  #Define  : 0
% 1.84/1.22  #Split   : 0
% 1.84/1.22  #Chain   : 0
% 1.84/1.22  #Close   : 0
% 1.84/1.22  
% 1.84/1.22  Ordering : KBO
% 1.84/1.22  
% 1.84/1.22  Simplification rules
% 1.84/1.22  ----------------------
% 1.84/1.22  #Subsume      : 0
% 1.84/1.22  #Demod        : 5
% 1.84/1.22  #Tautology    : 9
% 1.84/1.22  #SimpNegUnit  : 1
% 1.84/1.22  #BackRed      : 0
% 1.84/1.22  
% 1.84/1.22  #Partial instantiations: 0
% 1.84/1.22  #Strategies tried      : 1
% 1.84/1.22  
% 1.84/1.22  Timing (in seconds)
% 1.84/1.22  ----------------------
% 1.84/1.22  Preprocessing        : 0.25
% 1.84/1.22  Parsing              : 0.13
% 1.84/1.23  CNF conversion       : 0.02
% 1.84/1.23  Main loop            : 0.15
% 1.84/1.23  Inferencing          : 0.06
% 1.84/1.23  Reduction            : 0.04
% 1.84/1.23  Demodulation         : 0.03
% 1.84/1.23  BG Simplification    : 0.01
% 1.84/1.23  Subsumption          : 0.03
% 1.84/1.23  Abstraction          : 0.01
% 1.84/1.23  MUC search           : 0.00
% 1.84/1.23  Cooper               : 0.00
% 1.84/1.23  Total                : 0.42
% 1.84/1.23  Index Insertion      : 0.00
% 1.84/1.23  Index Deletion       : 0.00
% 1.84/1.23  Index Matching       : 0.00
% 1.84/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
