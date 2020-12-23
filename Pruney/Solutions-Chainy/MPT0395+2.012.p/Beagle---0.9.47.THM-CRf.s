%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:29 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  46 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_34,plain,(
    ~ r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_setfam_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_51,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_63,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_106,plain,(
    ! [D_39,B_40,A_41] :
      ( r2_hidden(D_39,B_40)
      | ~ r2_hidden(D_39,k3_xboole_0(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_121,plain,(
    ! [D_42] :
      ( r2_hidden(D_42,'#skF_6')
      | ~ r2_hidden(D_42,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_106])).

tff(c_126,plain,(
    ! [B_14] :
      ( r2_hidden('#skF_3'('#skF_5',B_14),'#skF_6')
      | r1_setfam_1('#skF_5',B_14) ) ),
    inference(resolution,[status(thm)],[c_32,c_121])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_49,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_46])).

tff(c_132,plain,(
    ! [A_47,B_48,D_49] :
      ( ~ r1_tarski('#skF_3'(A_47,B_48),D_49)
      | ~ r2_hidden(D_49,B_48)
      | r1_setfam_1(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_143,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_3'(A_50,B_51),B_51)
      | r1_setfam_1(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_49,c_132])).

tff(c_147,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_126,c_143])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:19:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.16  
% 1.61/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.16  %$ r2_hidden > r1_tarski > r1_setfam_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 1.61/1.16  
% 1.61/1.16  %Foreground sorts:
% 1.61/1.16  
% 1.61/1.16  
% 1.61/1.16  %Background operators:
% 1.61/1.16  
% 1.61/1.16  
% 1.61/1.16  %Foreground operators:
% 1.61/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.16  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.61/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.61/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.61/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.61/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.61/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.61/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.61/1.16  
% 1.61/1.17  tff(f_59, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 1.61/1.17  tff(f_54, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.61/1.17  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.61/1.17  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.61/1.17  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.61/1.17  tff(f_42, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.61/1.17  tff(c_34, plain, (~r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.61/1.17  tff(c_32, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), A_13) | r1_setfam_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.61/1.17  tff(c_36, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.61/1.17  tff(c_51, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.61/1.17  tff(c_63, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_36, c_51])).
% 1.61/1.17  tff(c_106, plain, (![D_39, B_40, A_41]: (r2_hidden(D_39, B_40) | ~r2_hidden(D_39, k3_xboole_0(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.61/1.17  tff(c_121, plain, (![D_42]: (r2_hidden(D_42, '#skF_6') | ~r2_hidden(D_42, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_106])).
% 1.61/1.17  tff(c_126, plain, (![B_14]: (r2_hidden('#skF_3'('#skF_5', B_14), '#skF_6') | r1_setfam_1('#skF_5', B_14))), inference(resolution, [status(thm)], [c_32, c_121])).
% 1.61/1.17  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.17  tff(c_46, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.17  tff(c_49, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_46])).
% 1.61/1.17  tff(c_132, plain, (![A_47, B_48, D_49]: (~r1_tarski('#skF_3'(A_47, B_48), D_49) | ~r2_hidden(D_49, B_48) | r1_setfam_1(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.61/1.17  tff(c_143, plain, (![A_50, B_51]: (~r2_hidden('#skF_3'(A_50, B_51), B_51) | r1_setfam_1(A_50, B_51))), inference(resolution, [status(thm)], [c_49, c_132])).
% 1.61/1.17  tff(c_147, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_126, c_143])).
% 1.61/1.17  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_147])).
% 1.61/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.17  
% 1.61/1.17  Inference rules
% 1.61/1.17  ----------------------
% 1.61/1.17  #Ref     : 0
% 1.61/1.17  #Sup     : 28
% 1.61/1.17  #Fact    : 0
% 1.61/1.17  #Define  : 0
% 1.61/1.17  #Split   : 0
% 1.61/1.17  #Chain   : 0
% 1.61/1.17  #Close   : 0
% 1.61/1.17  
% 1.61/1.17  Ordering : KBO
% 1.61/1.17  
% 1.61/1.17  Simplification rules
% 1.61/1.17  ----------------------
% 1.61/1.17  #Subsume      : 0
% 1.61/1.17  #Demod        : 1
% 1.61/1.17  #Tautology    : 14
% 1.61/1.17  #SimpNegUnit  : 1
% 1.61/1.17  #BackRed      : 0
% 1.61/1.17  
% 1.61/1.17  #Partial instantiations: 0
% 1.61/1.17  #Strategies tried      : 1
% 1.61/1.17  
% 1.61/1.17  Timing (in seconds)
% 1.61/1.17  ----------------------
% 1.61/1.17  Preprocessing        : 0.27
% 1.61/1.17  Parsing              : 0.14
% 1.61/1.17  CNF conversion       : 0.02
% 1.61/1.17  Main loop            : 0.13
% 1.61/1.17  Inferencing          : 0.05
% 1.61/1.17  Reduction            : 0.03
% 1.61/1.17  Demodulation         : 0.02
% 1.61/1.17  BG Simplification    : 0.01
% 1.61/1.17  Subsumption          : 0.03
% 1.61/1.17  Abstraction          : 0.01
% 1.61/1.17  MUC search           : 0.00
% 1.61/1.17  Cooper               : 0.00
% 1.61/1.17  Total                : 0.42
% 1.61/1.18  Index Insertion      : 0.00
% 1.61/1.18  Index Deletion       : 0.00
% 1.61/1.18  Index Matching       : 0.00
% 1.61/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
