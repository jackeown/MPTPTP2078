%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:29 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  51 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    ~ r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_169,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_3'(A_44,B_45),A_44)
      | r1_setfam_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_64,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_56])).

tff(c_91,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_91])).

tff(c_115,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_106])).

tff(c_148,plain,(
    ! [D_37,B_38,A_39] :
      ( r2_hidden(D_37,B_38)
      | ~ r2_hidden(D_37,k3_xboole_0(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_157,plain,(
    ! [D_37] :
      ( r2_hidden(D_37,'#skF_6')
      | ~ r2_hidden(D_37,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_148])).

tff(c_183,plain,(
    ! [B_45] :
      ( r2_hidden('#skF_3'('#skF_5',B_45),'#skF_6')
      | r1_setfam_1('#skF_5',B_45) ) ),
    inference(resolution,[status(thm)],[c_169,c_157])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_304,plain,(
    ! [A_62,B_63,D_64] :
      ( ~ r1_tarski('#skF_3'(A_62,B_63),D_64)
      | ~ r2_hidden(D_64,B_63)
      | r1_setfam_1(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_332,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden('#skF_3'(A_68,B_69),B_69)
      | r1_setfam_1(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_24,c_304])).

tff(c_340,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_183,c_332])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.22  
% 2.02/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.22  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.02/1.22  
% 2.02/1.22  %Foreground sorts:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Background operators:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Foreground operators:
% 2.02/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.22  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.02/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.02/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.02/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.02/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.22  
% 2.02/1.23  tff(f_65, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_setfam_1)).
% 2.02/1.23  tff(f_60, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.02/1.23  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.02/1.23  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.02/1.23  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.02/1.23  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.02/1.23  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.02/1.23  tff(c_42, plain, (~r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.02/1.23  tff(c_169, plain, (![A_44, B_45]: (r2_hidden('#skF_3'(A_44, B_45), A_44) | r1_setfam_1(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.02/1.23  tff(c_30, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.23  tff(c_44, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.02/1.23  tff(c_56, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.23  tff(c_64, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_56])).
% 2.02/1.23  tff(c_91, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.23  tff(c_106, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_64, c_91])).
% 2.02/1.23  tff(c_115, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_106])).
% 2.02/1.23  tff(c_148, plain, (![D_37, B_38, A_39]: (r2_hidden(D_37, B_38) | ~r2_hidden(D_37, k3_xboole_0(A_39, B_38)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.23  tff(c_157, plain, (![D_37]: (r2_hidden(D_37, '#skF_6') | ~r2_hidden(D_37, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_148])).
% 2.02/1.23  tff(c_183, plain, (![B_45]: (r2_hidden('#skF_3'('#skF_5', B_45), '#skF_6') | r1_setfam_1('#skF_5', B_45))), inference(resolution, [status(thm)], [c_169, c_157])).
% 2.02/1.23  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.02/1.23  tff(c_304, plain, (![A_62, B_63, D_64]: (~r1_tarski('#skF_3'(A_62, B_63), D_64) | ~r2_hidden(D_64, B_63) | r1_setfam_1(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.02/1.23  tff(c_332, plain, (![A_68, B_69]: (~r2_hidden('#skF_3'(A_68, B_69), B_69) | r1_setfam_1(A_68, B_69))), inference(resolution, [status(thm)], [c_24, c_304])).
% 2.02/1.23  tff(c_340, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_183, c_332])).
% 2.02/1.23  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_340])).
% 2.02/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.23  
% 2.02/1.23  Inference rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Ref     : 0
% 2.02/1.23  #Sup     : 73
% 2.02/1.23  #Fact    : 0
% 2.02/1.23  #Define  : 0
% 2.02/1.23  #Split   : 1
% 2.02/1.23  #Chain   : 0
% 2.02/1.23  #Close   : 0
% 2.02/1.23  
% 2.02/1.23  Ordering : KBO
% 2.02/1.23  
% 2.02/1.23  Simplification rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Subsume      : 7
% 2.02/1.23  #Demod        : 17
% 2.02/1.23  #Tautology    : 38
% 2.02/1.23  #SimpNegUnit  : 1
% 2.02/1.23  #BackRed      : 0
% 2.02/1.23  
% 2.02/1.23  #Partial instantiations: 0
% 2.02/1.23  #Strategies tried      : 1
% 2.02/1.23  
% 2.02/1.23  Timing (in seconds)
% 2.02/1.23  ----------------------
% 2.07/1.23  Preprocessing        : 0.28
% 2.07/1.23  Parsing              : 0.15
% 2.07/1.23  CNF conversion       : 0.02
% 2.07/1.23  Main loop            : 0.20
% 2.07/1.23  Inferencing          : 0.07
% 2.07/1.23  Reduction            : 0.06
% 2.07/1.23  Demodulation         : 0.04
% 2.07/1.23  BG Simplification    : 0.01
% 2.07/1.23  Subsumption          : 0.04
% 2.07/1.23  Abstraction          : 0.01
% 2.07/1.23  MUC search           : 0.00
% 2.07/1.23  Cooper               : 0.00
% 2.07/1.23  Total                : 0.50
% 2.07/1.23  Index Insertion      : 0.00
% 2.07/1.23  Index Deletion       : 0.00
% 2.07/1.23  Index Matching       : 0.00
% 2.07/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
