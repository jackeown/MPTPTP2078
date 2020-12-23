%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:55 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  65 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k10_relat_1(C,A),k10_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t180_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_10,A_9,C_12] :
      ( r1_tarski(k10_relat_1(B_10,A_9),k10_relat_1(C_12,A_9))
      | ~ r1_tarski(B_10,C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_19,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_27,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_19])).

tff(c_50,plain,(
    ! [C_22,A_23,B_24] :
      ( k2_xboole_0(k10_relat_1(C_22,A_23),k10_relat_1(C_22,B_24)) = k10_relat_1(C_22,k2_xboole_0(A_23,B_24))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [C_28,A_29,C_30,B_31] :
      ( r1_tarski(k10_relat_1(C_28,A_29),C_30)
      | ~ r1_tarski(k10_relat_1(C_28,k2_xboole_0(A_29,B_31)),C_30)
      | ~ v1_relat_1(C_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2])).

tff(c_105,plain,(
    ! [C_35,C_36] :
      ( r1_tarski(k10_relat_1(C_35,'#skF_1'),C_36)
      | ~ r1_tarski(k10_relat_1(C_35,'#skF_2'),C_36)
      | ~ v1_relat_1(C_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_67])).

tff(c_122,plain,(
    ! [B_41,C_42] :
      ( r1_tarski(k10_relat_1(B_41,'#skF_1'),k10_relat_1(C_42,'#skF_2'))
      | ~ r1_tarski(B_41,C_42)
      | ~ v1_relat_1(C_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_8,c_105])).

tff(c_10,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_125,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_122,c_10])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.21  
% 1.85/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.21  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.85/1.21  
% 1.85/1.21  %Foreground sorts:
% 1.85/1.21  
% 1.85/1.21  
% 1.85/1.21  %Background operators:
% 1.85/1.21  
% 1.85/1.21  
% 1.85/1.21  %Foreground operators:
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.85/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.21  
% 1.85/1.22  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k10_relat_1(C, A), k10_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t180_relat_1)).
% 1.85/1.22  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t179_relat_1)).
% 1.85/1.22  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.85/1.22  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 1.85/1.22  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.85/1.22  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.85/1.22  tff(c_16, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.85/1.22  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.85/1.22  tff(c_8, plain, (![B_10, A_9, C_12]: (r1_tarski(k10_relat_1(B_10, A_9), k10_relat_1(C_12, A_9)) | ~r1_tarski(B_10, C_12) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.85/1.22  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.85/1.22  tff(c_19, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.85/1.22  tff(c_27, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_19])).
% 1.85/1.22  tff(c_50, plain, (![C_22, A_23, B_24]: (k2_xboole_0(k10_relat_1(C_22, A_23), k10_relat_1(C_22, B_24))=k10_relat_1(C_22, k2_xboole_0(A_23, B_24)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.85/1.22  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.85/1.22  tff(c_67, plain, (![C_28, A_29, C_30, B_31]: (r1_tarski(k10_relat_1(C_28, A_29), C_30) | ~r1_tarski(k10_relat_1(C_28, k2_xboole_0(A_29, B_31)), C_30) | ~v1_relat_1(C_28))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2])).
% 1.85/1.22  tff(c_105, plain, (![C_35, C_36]: (r1_tarski(k10_relat_1(C_35, '#skF_1'), C_36) | ~r1_tarski(k10_relat_1(C_35, '#skF_2'), C_36) | ~v1_relat_1(C_35))), inference(superposition, [status(thm), theory('equality')], [c_27, c_67])).
% 1.85/1.22  tff(c_122, plain, (![B_41, C_42]: (r1_tarski(k10_relat_1(B_41, '#skF_1'), k10_relat_1(C_42, '#skF_2')) | ~r1_tarski(B_41, C_42) | ~v1_relat_1(C_42) | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_8, c_105])).
% 1.85/1.22  tff(c_10, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.85/1.22  tff(c_125, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_122, c_10])).
% 1.85/1.22  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_14, c_125])).
% 1.85/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.22  
% 1.85/1.22  Inference rules
% 1.85/1.22  ----------------------
% 1.85/1.22  #Ref     : 0
% 1.85/1.22  #Sup     : 28
% 1.85/1.22  #Fact    : 0
% 1.85/1.22  #Define  : 0
% 1.85/1.22  #Split   : 0
% 1.85/1.22  #Chain   : 0
% 1.85/1.22  #Close   : 0
% 1.85/1.22  
% 1.85/1.22  Ordering : KBO
% 1.85/1.22  
% 1.85/1.22  Simplification rules
% 1.85/1.22  ----------------------
% 1.85/1.22  #Subsume      : 0
% 1.85/1.22  #Demod        : 3
% 1.85/1.22  #Tautology    : 8
% 1.85/1.22  #SimpNegUnit  : 0
% 1.85/1.22  #BackRed      : 0
% 1.85/1.22  
% 1.85/1.22  #Partial instantiations: 0
% 1.85/1.23  #Strategies tried      : 1
% 1.85/1.23  
% 1.85/1.23  Timing (in seconds)
% 1.85/1.23  ----------------------
% 1.96/1.23  Preprocessing        : 0.27
% 1.96/1.23  Parsing              : 0.16
% 1.96/1.23  CNF conversion       : 0.02
% 1.96/1.23  Main loop            : 0.16
% 1.96/1.23  Inferencing          : 0.07
% 1.96/1.23  Reduction            : 0.04
% 1.96/1.23  Demodulation         : 0.03
% 1.96/1.23  BG Simplification    : 0.01
% 1.96/1.23  Subsumption          : 0.03
% 1.96/1.23  Abstraction          : 0.01
% 1.96/1.23  MUC search           : 0.00
% 1.96/1.23  Cooper               : 0.00
% 1.96/1.23  Total                : 0.46
% 1.96/1.23  Index Insertion      : 0.00
% 1.96/1.23  Index Deletion       : 0.00
% 1.96/1.23  Index Matching       : 0.00
% 1.96/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
