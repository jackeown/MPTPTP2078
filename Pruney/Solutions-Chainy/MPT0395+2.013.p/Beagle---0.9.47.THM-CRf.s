%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:30 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  46 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_34,plain,(
    ~ r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),A_12)
      | r1_setfam_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_51,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_63,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_106,plain,(
    ! [D_38,B_39,A_40] :
      ( r2_hidden(D_38,B_39)
      | ~ r2_hidden(D_38,k3_xboole_0(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_121,plain,(
    ! [D_41] :
      ( r2_hidden(D_41,'#skF_6')
      | ~ r2_hidden(D_41,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_106])).

tff(c_126,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_3'('#skF_5',B_13),'#skF_6')
      | r1_setfam_1('#skF_5',B_13) ) ),
    inference(resolution,[status(thm)],[c_32,c_121])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_49,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_46])).

tff(c_132,plain,(
    ! [A_46,B_47,D_48] :
      ( ~ r1_tarski('#skF_3'(A_46,B_47),D_48)
      | ~ r2_hidden(D_48,B_47)
      | r1_setfam_1(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_143,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden('#skF_3'(A_49,B_50),B_50)
      | r1_setfam_1(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_49,c_132])).

tff(c_147,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_126,c_143])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:56:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.15  
% 1.61/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.15  %$ r2_hidden > r1_tarski > r1_setfam_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 1.61/1.15  
% 1.61/1.15  %Foreground sorts:
% 1.61/1.15  
% 1.61/1.15  
% 1.61/1.15  %Background operators:
% 1.61/1.15  
% 1.61/1.15  
% 1.61/1.15  %Foreground operators:
% 1.61/1.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.15  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.61/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.61/1.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.61/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.61/1.15  tff('#skF_6', type, '#skF_6': $i).
% 1.61/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.61/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.61/1.15  
% 1.61/1.16  tff(f_59, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 1.61/1.16  tff(f_54, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.61/1.16  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.61/1.16  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.61/1.16  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.61/1.16  tff(f_42, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.61/1.16  tff(c_34, plain, (~r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.61/1.16  tff(c_32, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), A_12) | r1_setfam_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.61/1.16  tff(c_36, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.61/1.16  tff(c_51, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.61/1.16  tff(c_63, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_36, c_51])).
% 1.61/1.16  tff(c_106, plain, (![D_38, B_39, A_40]: (r2_hidden(D_38, B_39) | ~r2_hidden(D_38, k3_xboole_0(A_40, B_39)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.61/1.16  tff(c_121, plain, (![D_41]: (r2_hidden(D_41, '#skF_6') | ~r2_hidden(D_41, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_106])).
% 1.61/1.16  tff(c_126, plain, (![B_13]: (r2_hidden('#skF_3'('#skF_5', B_13), '#skF_6') | r1_setfam_1('#skF_5', B_13))), inference(resolution, [status(thm)], [c_32, c_121])).
% 1.61/1.16  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.16  tff(c_46, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.16  tff(c_49, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_46])).
% 1.61/1.16  tff(c_132, plain, (![A_46, B_47, D_48]: (~r1_tarski('#skF_3'(A_46, B_47), D_48) | ~r2_hidden(D_48, B_47) | r1_setfam_1(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.61/1.16  tff(c_143, plain, (![A_49, B_50]: (~r2_hidden('#skF_3'(A_49, B_50), B_50) | r1_setfam_1(A_49, B_50))), inference(resolution, [status(thm)], [c_49, c_132])).
% 1.61/1.16  tff(c_147, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_126, c_143])).
% 1.61/1.16  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_147])).
% 1.61/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.16  
% 1.61/1.16  Inference rules
% 1.61/1.16  ----------------------
% 1.61/1.16  #Ref     : 0
% 1.61/1.16  #Sup     : 28
% 1.61/1.16  #Fact    : 0
% 1.61/1.16  #Define  : 0
% 1.61/1.16  #Split   : 0
% 1.61/1.16  #Chain   : 0
% 1.61/1.16  #Close   : 0
% 1.61/1.16  
% 1.61/1.16  Ordering : KBO
% 1.61/1.16  
% 1.61/1.16  Simplification rules
% 1.61/1.16  ----------------------
% 1.61/1.16  #Subsume      : 0
% 1.61/1.16  #Demod        : 1
% 1.61/1.16  #Tautology    : 14
% 1.61/1.16  #SimpNegUnit  : 1
% 1.61/1.16  #BackRed      : 0
% 1.61/1.16  
% 1.61/1.16  #Partial instantiations: 0
% 1.61/1.16  #Strategies tried      : 1
% 1.61/1.16  
% 1.61/1.16  Timing (in seconds)
% 1.61/1.16  ----------------------
% 1.61/1.16  Preprocessing        : 0.27
% 1.61/1.16  Parsing              : 0.14
% 1.61/1.16  CNF conversion       : 0.02
% 1.61/1.16  Main loop            : 0.13
% 1.61/1.16  Inferencing          : 0.05
% 1.61/1.16  Reduction            : 0.03
% 1.61/1.16  Demodulation         : 0.02
% 1.61/1.16  BG Simplification    : 0.01
% 1.61/1.16  Subsumption          : 0.03
% 1.61/1.16  Abstraction          : 0.01
% 1.61/1.16  MUC search           : 0.00
% 1.61/1.16  Cooper               : 0.00
% 1.61/1.16  Total                : 0.42
% 1.61/1.16  Index Insertion      : 0.00
% 1.61/1.16  Index Deletion       : 0.00
% 1.61/1.16  Index Matching       : 0.00
% 1.61/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
