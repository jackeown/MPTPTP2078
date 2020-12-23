%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:53 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  46 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_146,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_170,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_146])).

tff(c_177,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_170])).

tff(c_249,plain,(
    ! [C_38,A_39,B_40] :
      ( r1_tarski(k10_relat_1(C_38,k3_xboole_0(A_39,B_40)),k3_xboole_0(k10_relat_1(C_38,A_39),k10_relat_1(C_38,B_40)))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_263,plain,(
    ! [C_38] :
      ( r1_tarski(k10_relat_1(C_38,'#skF_1'),k3_xboole_0(k10_relat_1(C_38,'#skF_1'),k10_relat_1(C_38,'#skF_2')))
      | ~ v1_relat_1(C_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_249])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_320,plain,(
    ! [A_42,A_43,B_44] :
      ( r1_tarski(A_42,A_43)
      | ~ r1_tarski(A_42,k3_xboole_0(A_43,B_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_10])).

tff(c_409,plain,(
    ! [A_54,B_55,A_56] :
      ( r1_tarski(A_54,B_55)
      | ~ r1_tarski(A_54,k3_xboole_0(A_56,B_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_320])).

tff(c_1033,plain,(
    ! [C_85] :
      ( r1_tarski(k10_relat_1(C_85,'#skF_1'),k10_relat_1(C_85,'#skF_2'))
      | ~ v1_relat_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_263,c_409])).

tff(c_18,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1038,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1033,c_18])).

tff(c_1046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1038])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:05:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.43  
% 2.74/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.43  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.43  
% 2.74/1.43  %Foreground sorts:
% 2.74/1.43  
% 2.74/1.43  
% 2.74/1.43  %Background operators:
% 2.74/1.43  
% 2.74/1.43  
% 2.74/1.43  %Foreground operators:
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.74/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.74/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.43  
% 2.74/1.44  tff(f_52, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 2.74/1.44  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.74/1.44  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.74/1.44  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.74/1.44  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_relat_1)).
% 2.74/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.74/1.44  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.74/1.44  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.74/1.44  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.44  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.74/1.44  tff(c_65, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.44  tff(c_69, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_65])).
% 2.74/1.44  tff(c_146, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.44  tff(c_170, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_69, c_146])).
% 2.74/1.44  tff(c_177, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_170])).
% 2.74/1.44  tff(c_249, plain, (![C_38, A_39, B_40]: (r1_tarski(k10_relat_1(C_38, k3_xboole_0(A_39, B_40)), k3_xboole_0(k10_relat_1(C_38, A_39), k10_relat_1(C_38, B_40))) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.74/1.44  tff(c_263, plain, (![C_38]: (r1_tarski(k10_relat_1(C_38, '#skF_1'), k3_xboole_0(k10_relat_1(C_38, '#skF_1'), k10_relat_1(C_38, '#skF_2'))) | ~v1_relat_1(C_38))), inference(superposition, [status(thm), theory('equality')], [c_177, c_249])).
% 2.74/1.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.44  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, B_6) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.44  tff(c_320, plain, (![A_42, A_43, B_44]: (r1_tarski(A_42, A_43) | ~r1_tarski(A_42, k3_xboole_0(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_10])).
% 2.74/1.44  tff(c_409, plain, (![A_54, B_55, A_56]: (r1_tarski(A_54, B_55) | ~r1_tarski(A_54, k3_xboole_0(A_56, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_320])).
% 2.74/1.44  tff(c_1033, plain, (![C_85]: (r1_tarski(k10_relat_1(C_85, '#skF_1'), k10_relat_1(C_85, '#skF_2')) | ~v1_relat_1(C_85))), inference(resolution, [status(thm)], [c_263, c_409])).
% 2.74/1.44  tff(c_18, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.74/1.44  tff(c_1038, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1033, c_18])).
% 2.74/1.44  tff(c_1046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1038])).
% 2.74/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.44  
% 2.74/1.44  Inference rules
% 2.74/1.44  ----------------------
% 2.74/1.44  #Ref     : 3
% 2.74/1.44  #Sup     : 276
% 2.74/1.44  #Fact    : 0
% 2.74/1.44  #Define  : 0
% 2.74/1.44  #Split   : 8
% 2.74/1.44  #Chain   : 0
% 2.74/1.44  #Close   : 0
% 2.74/1.44  
% 2.74/1.44  Ordering : KBO
% 2.74/1.44  
% 2.74/1.44  Simplification rules
% 2.74/1.44  ----------------------
% 2.74/1.44  #Subsume      : 111
% 2.74/1.44  #Demod        : 62
% 2.74/1.44  #Tautology    : 76
% 2.74/1.44  #SimpNegUnit  : 6
% 2.74/1.44  #BackRed      : 4
% 2.74/1.44  
% 2.74/1.44  #Partial instantiations: 0
% 2.74/1.44  #Strategies tried      : 1
% 2.74/1.44  
% 2.74/1.44  Timing (in seconds)
% 2.74/1.44  ----------------------
% 2.74/1.45  Preprocessing        : 0.27
% 2.74/1.45  Parsing              : 0.15
% 2.74/1.45  CNF conversion       : 0.02
% 2.74/1.45  Main loop            : 0.42
% 2.74/1.45  Inferencing          : 0.16
% 2.74/1.45  Reduction            : 0.13
% 2.74/1.45  Demodulation         : 0.09
% 2.74/1.45  BG Simplification    : 0.02
% 2.74/1.45  Subsumption          : 0.08
% 2.74/1.45  Abstraction          : 0.02
% 2.74/1.45  MUC search           : 0.00
% 2.74/1.45  Cooper               : 0.00
% 2.74/1.45  Total                : 0.71
% 2.74/1.45  Index Insertion      : 0.00
% 2.74/1.45  Index Deletion       : 0.00
% 2.74/1.45  Index Matching       : 0.00
% 2.74/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
