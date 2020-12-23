%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:56 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  89 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_23,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(A_20,C_21)
      | ~ r1_tarski(B_22,C_21)
      | ~ r1_tarski(A_20,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_23] :
      ( r1_tarski(A_23,'#skF_4')
      | ~ r1_tarski(A_23,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_23])).

tff(c_37,plain,(
    ! [A_13] :
      ( r1_tarski(k7_relat_1('#skF_3',A_13),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_33])).

tff(c_40,plain,(
    ! [A_13] : r1_tarski(k7_relat_1('#skF_3',A_13),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_37])).

tff(c_6,plain,(
    ! [C_8,A_6,B_7] :
      ( k7_relat_1(k7_relat_1(C_8,A_6),B_7) = k7_relat_1(C_8,A_6)
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_170,plain,(
    ! [B_46,A_47,C_48] :
      ( r1_tarski(k7_relat_1(B_46,A_47),k7_relat_1(C_48,A_47))
      | ~ r1_tarski(B_46,C_48)
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1702,plain,(
    ! [C_129,A_130,C_131,B_132] :
      ( r1_tarski(k7_relat_1(C_129,A_130),k7_relat_1(C_131,B_132))
      | ~ r1_tarski(k7_relat_1(C_129,A_130),C_131)
      | ~ v1_relat_1(C_131)
      | ~ v1_relat_1(k7_relat_1(C_129,A_130))
      | ~ r1_tarski(A_130,B_132)
      | ~ v1_relat_1(C_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_170])).

tff(c_12,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1745,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1702,c_12])).

tff(c_1791,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_18,c_40,c_1745])).

tff(c_1794,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_1791])).

tff(c_1798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.66  
% 3.94/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.66  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.94/1.66  
% 3.94/1.66  %Foreground sorts:
% 3.94/1.66  
% 3.94/1.66  
% 3.94/1.66  %Background operators:
% 3.94/1.66  
% 3.94/1.66  
% 3.94/1.66  %Foreground operators:
% 3.94/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.94/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.94/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.94/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.94/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.94/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.94/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.94/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.66  
% 3.94/1.67  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 3.94/1.67  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.94/1.67  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 3.94/1.67  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.94/1.67  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 3.94/1.67  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 3.94/1.67  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.94/1.67  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.94/1.67  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.94/1.67  tff(c_18, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.94/1.67  tff(c_10, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.94/1.67  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.94/1.67  tff(c_23, plain, (![A_20, C_21, B_22]: (r1_tarski(A_20, C_21) | ~r1_tarski(B_22, C_21) | ~r1_tarski(A_20, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.94/1.67  tff(c_33, plain, (![A_23]: (r1_tarski(A_23, '#skF_4') | ~r1_tarski(A_23, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_23])).
% 3.94/1.67  tff(c_37, plain, (![A_13]: (r1_tarski(k7_relat_1('#skF_3', A_13), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_33])).
% 3.94/1.67  tff(c_40, plain, (![A_13]: (r1_tarski(k7_relat_1('#skF_3', A_13), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_37])).
% 3.94/1.67  tff(c_6, plain, (![C_8, A_6, B_7]: (k7_relat_1(k7_relat_1(C_8, A_6), B_7)=k7_relat_1(C_8, A_6) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.94/1.67  tff(c_170, plain, (![B_46, A_47, C_48]: (r1_tarski(k7_relat_1(B_46, A_47), k7_relat_1(C_48, A_47)) | ~r1_tarski(B_46, C_48) | ~v1_relat_1(C_48) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.94/1.67  tff(c_1702, plain, (![C_129, A_130, C_131, B_132]: (r1_tarski(k7_relat_1(C_129, A_130), k7_relat_1(C_131, B_132)) | ~r1_tarski(k7_relat_1(C_129, A_130), C_131) | ~v1_relat_1(C_131) | ~v1_relat_1(k7_relat_1(C_129, A_130)) | ~r1_tarski(A_130, B_132) | ~v1_relat_1(C_129))), inference(superposition, [status(thm), theory('equality')], [c_6, c_170])).
% 3.94/1.67  tff(c_12, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.94/1.67  tff(c_1745, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1702, c_12])).
% 3.94/1.67  tff(c_1791, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_18, c_40, c_1745])).
% 3.94/1.67  tff(c_1794, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_1791])).
% 3.94/1.67  tff(c_1798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_1794])).
% 3.94/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.67  
% 3.94/1.67  Inference rules
% 3.94/1.67  ----------------------
% 3.94/1.67  #Ref     : 0
% 3.94/1.67  #Sup     : 453
% 3.94/1.67  #Fact    : 0
% 3.94/1.67  #Define  : 0
% 3.94/1.67  #Split   : 6
% 3.94/1.67  #Chain   : 0
% 3.94/1.67  #Close   : 0
% 3.94/1.67  
% 3.94/1.67  Ordering : KBO
% 3.94/1.67  
% 3.94/1.67  Simplification rules
% 3.94/1.67  ----------------------
% 3.94/1.67  #Subsume      : 166
% 3.94/1.67  #Demod        : 137
% 3.94/1.67  #Tautology    : 33
% 3.94/1.67  #SimpNegUnit  : 0
% 3.94/1.67  #BackRed      : 0
% 3.94/1.67  
% 3.94/1.67  #Partial instantiations: 0
% 3.94/1.67  #Strategies tried      : 1
% 3.94/1.67  
% 3.94/1.67  Timing (in seconds)
% 3.94/1.67  ----------------------
% 3.94/1.67  Preprocessing        : 0.27
% 3.94/1.67  Parsing              : 0.15
% 3.94/1.67  CNF conversion       : 0.02
% 3.94/1.67  Main loop            : 0.65
% 3.94/1.67  Inferencing          : 0.21
% 3.94/1.67  Reduction            : 0.16
% 3.94/1.67  Demodulation         : 0.11
% 3.94/1.67  BG Simplification    : 0.03
% 3.94/1.67  Subsumption          : 0.22
% 3.94/1.67  Abstraction          : 0.03
% 3.94/1.67  MUC search           : 0.00
% 3.94/1.67  Cooper               : 0.00
% 3.94/1.67  Total                : 0.94
% 3.94/1.67  Index Insertion      : 0.00
% 3.94/1.67  Index Deletion       : 0.00
% 3.94/1.67  Index Matching       : 0.00
% 3.94/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
