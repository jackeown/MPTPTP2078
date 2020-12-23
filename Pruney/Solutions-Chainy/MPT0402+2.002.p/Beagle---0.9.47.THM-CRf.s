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
% DateTime   : Thu Dec  3 09:57:41 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :   33 (  43 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  84 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_setfam_1(C,k2_tarski(A,B))
       => ! [D] :
            ~ ( r2_hidden(D,C)
              & ~ r1_tarski(D,A)
              & ~ r1_tarski(D,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_30,plain,(
    ~ r1_tarski('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    r1_setfam_1('#skF_7',k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_55,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden('#skF_4'(A_32,B_33,C_34),B_33)
      | ~ r2_hidden(C_34,A_32)
      | ~ r1_setfam_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6103,plain,(
    ! [A_3545,A_3546,B_3547,C_3548] :
      ( '#skF_4'(A_3545,k2_tarski(A_3546,B_3547),C_3548) = B_3547
      | '#skF_4'(A_3545,k2_tarski(A_3546,B_3547),C_3548) = A_3546
      | ~ r2_hidden(C_3548,A_3545)
      | ~ r1_setfam_1(A_3545,k2_tarski(A_3546,B_3547)) ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_6185,plain,(
    ! [C_3601] :
      ( '#skF_4'('#skF_7',k2_tarski('#skF_5','#skF_6'),C_3601) = '#skF_6'
      | '#skF_4'('#skF_7',k2_tarski('#skF_5','#skF_6'),C_3601) = '#skF_5'
      | ~ r2_hidden(C_3601,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_34,c_6103])).

tff(c_20,plain,(
    ! [C_17,A_7,B_8] :
      ( r1_tarski(C_17,'#skF_4'(A_7,B_8,C_17))
      | ~ r2_hidden(C_17,A_7)
      | ~ r1_setfam_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6195,plain,(
    ! [C_3601] :
      ( r1_tarski(C_3601,'#skF_5')
      | ~ r2_hidden(C_3601,'#skF_7')
      | ~ r1_setfam_1('#skF_7',k2_tarski('#skF_5','#skF_6'))
      | '#skF_4'('#skF_7',k2_tarski('#skF_5','#skF_6'),C_3601) = '#skF_6'
      | ~ r2_hidden(C_3601,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6185,c_20])).

tff(c_6379,plain,(
    ! [C_3760] :
      ( r1_tarski(C_3760,'#skF_5')
      | '#skF_4'('#skF_7',k2_tarski('#skF_5','#skF_6'),C_3760) = '#skF_6'
      | ~ r2_hidden(C_3760,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6195])).

tff(c_6392,plain,(
    ! [C_3760] :
      ( r1_tarski(C_3760,'#skF_6')
      | ~ r2_hidden(C_3760,'#skF_7')
      | ~ r1_setfam_1('#skF_7',k2_tarski('#skF_5','#skF_6'))
      | r1_tarski(C_3760,'#skF_5')
      | ~ r2_hidden(C_3760,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6379,c_20])).

tff(c_6491,plain,(
    ! [C_3813] :
      ( r1_tarski(C_3813,'#skF_6')
      | r1_tarski(C_3813,'#skF_5')
      | ~ r2_hidden(C_3813,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6392])).

tff(c_6524,plain,
    ( r1_tarski('#skF_8','#skF_6')
    | r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_6491])).

tff(c_6537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_6524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:52:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.71/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.18  
% 5.71/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.18  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8
% 5.71/2.18  
% 5.71/2.18  %Foreground sorts:
% 5.71/2.18  
% 5.71/2.18  
% 5.71/2.18  %Background operators:
% 5.71/2.18  
% 5.71/2.18  
% 5.71/2.18  %Foreground operators:
% 5.71/2.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.71/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.71/2.18  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 5.71/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.71/2.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.71/2.18  tff('#skF_7', type, '#skF_7': $i).
% 5.71/2.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.71/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.71/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.71/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.71/2.18  tff('#skF_6', type, '#skF_6': $i).
% 5.71/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.71/2.18  tff('#skF_8', type, '#skF_8': $i).
% 5.71/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.71/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.71/2.18  
% 5.71/2.19  tff(f_59, negated_conjecture, ~(![A, B, C]: (r1_setfam_1(C, k2_tarski(A, B)) => (![D]: ~((r2_hidden(D, C) & ~r1_tarski(D, A)) & ~r1_tarski(D, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_setfam_1)).
% 5.71/2.19  tff(f_46, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 5.71/2.19  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.71/2.19  tff(c_30, plain, (~r1_tarski('#skF_8', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.71/2.19  tff(c_28, plain, (~r1_tarski('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.71/2.19  tff(c_32, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.71/2.19  tff(c_34, plain, (r1_setfam_1('#skF_7', k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.71/2.19  tff(c_55, plain, (![A_32, B_33, C_34]: (r2_hidden('#skF_4'(A_32, B_33, C_34), B_33) | ~r2_hidden(C_34, A_32) | ~r1_setfam_1(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.71/2.19  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.71/2.19  tff(c_6103, plain, (![A_3545, A_3546, B_3547, C_3548]: ('#skF_4'(A_3545, k2_tarski(A_3546, B_3547), C_3548)=B_3547 | '#skF_4'(A_3545, k2_tarski(A_3546, B_3547), C_3548)=A_3546 | ~r2_hidden(C_3548, A_3545) | ~r1_setfam_1(A_3545, k2_tarski(A_3546, B_3547)))), inference(resolution, [status(thm)], [c_55, c_2])).
% 5.71/2.19  tff(c_6185, plain, (![C_3601]: ('#skF_4'('#skF_7', k2_tarski('#skF_5', '#skF_6'), C_3601)='#skF_6' | '#skF_4'('#skF_7', k2_tarski('#skF_5', '#skF_6'), C_3601)='#skF_5' | ~r2_hidden(C_3601, '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_6103])).
% 5.71/2.19  tff(c_20, plain, (![C_17, A_7, B_8]: (r1_tarski(C_17, '#skF_4'(A_7, B_8, C_17)) | ~r2_hidden(C_17, A_7) | ~r1_setfam_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.71/2.19  tff(c_6195, plain, (![C_3601]: (r1_tarski(C_3601, '#skF_5') | ~r2_hidden(C_3601, '#skF_7') | ~r1_setfam_1('#skF_7', k2_tarski('#skF_5', '#skF_6')) | '#skF_4'('#skF_7', k2_tarski('#skF_5', '#skF_6'), C_3601)='#skF_6' | ~r2_hidden(C_3601, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6185, c_20])).
% 5.71/2.19  tff(c_6379, plain, (![C_3760]: (r1_tarski(C_3760, '#skF_5') | '#skF_4'('#skF_7', k2_tarski('#skF_5', '#skF_6'), C_3760)='#skF_6' | ~r2_hidden(C_3760, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6195])).
% 5.71/2.19  tff(c_6392, plain, (![C_3760]: (r1_tarski(C_3760, '#skF_6') | ~r2_hidden(C_3760, '#skF_7') | ~r1_setfam_1('#skF_7', k2_tarski('#skF_5', '#skF_6')) | r1_tarski(C_3760, '#skF_5') | ~r2_hidden(C_3760, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6379, c_20])).
% 5.71/2.19  tff(c_6491, plain, (![C_3813]: (r1_tarski(C_3813, '#skF_6') | r1_tarski(C_3813, '#skF_5') | ~r2_hidden(C_3813, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6392])).
% 5.71/2.19  tff(c_6524, plain, (r1_tarski('#skF_8', '#skF_6') | r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_6491])).
% 5.71/2.19  tff(c_6537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_6524])).
% 5.71/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.19  
% 5.71/2.19  Inference rules
% 5.71/2.19  ----------------------
% 5.71/2.19  #Ref     : 0
% 5.71/2.19  #Sup     : 1133
% 5.71/2.19  #Fact    : 39
% 5.71/2.19  #Define  : 0
% 5.71/2.19  #Split   : 10
% 5.71/2.19  #Chain   : 0
% 5.71/2.19  #Close   : 0
% 5.71/2.19  
% 5.71/2.19  Ordering : KBO
% 5.71/2.19  
% 5.71/2.19  Simplification rules
% 5.71/2.19  ----------------------
% 5.71/2.19  #Subsume      : 352
% 5.71/2.19  #Demod        : 8
% 5.71/2.19  #Tautology    : 307
% 5.71/2.19  #SimpNegUnit  : 3
% 5.71/2.19  #BackRed      : 0
% 5.71/2.19  
% 5.71/2.19  #Partial instantiations: 2556
% 5.71/2.19  #Strategies tried      : 1
% 5.71/2.19  
% 5.71/2.19  Timing (in seconds)
% 5.71/2.19  ----------------------
% 5.71/2.19  Preprocessing        : 0.27
% 5.71/2.19  Parsing              : 0.14
% 5.71/2.19  CNF conversion       : 0.02
% 5.71/2.19  Main loop            : 1.16
% 5.71/2.19  Inferencing          : 0.55
% 5.71/2.19  Reduction            : 0.21
% 5.71/2.19  Demodulation         : 0.14
% 5.71/2.19  BG Simplification    : 0.06
% 5.71/2.19  Subsumption          : 0.27
% 5.71/2.19  Abstraction          : 0.07
% 5.71/2.19  MUC search           : 0.00
% 5.71/2.19  Cooper               : 0.00
% 5.71/2.19  Total                : 1.45
% 5.71/2.19  Index Insertion      : 0.00
% 5.71/2.19  Index Deletion       : 0.00
% 5.71/2.19  Index Matching       : 0.00
% 5.71/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
