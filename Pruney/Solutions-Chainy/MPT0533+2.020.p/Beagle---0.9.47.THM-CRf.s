%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:19 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   45 (  65 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(k8_relat_1(A_4,C_6),k8_relat_1(B_5,C_6))
      | ~ r1_tarski(A_4,B_5)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ! [A_22,B_23,C_24] :
      ( r1_tarski(k8_relat_1(A_22,B_23),k8_relat_1(A_22,C_24))
      | ~ r1_tarski(B_23,C_24)
      | ~ v1_relat_1(C_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_33,A_34,C_35,B_36] :
      ( r1_tarski(A_33,k8_relat_1(A_34,C_35))
      | ~ r1_tarski(A_33,k8_relat_1(A_34,B_36))
      | ~ r1_tarski(B_36,C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_198,plain,(
    ! [A_56,C_57,B_58,C_59] :
      ( r1_tarski(k8_relat_1(A_56,C_57),k8_relat_1(B_58,C_59))
      | ~ r1_tarski(C_57,C_59)
      | ~ v1_relat_1(C_59)
      | ~ r1_tarski(A_56,B_58)
      | ~ v1_relat_1(C_57) ) ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_8,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_215,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_198,c_8])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10,c_14,c_12,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.25  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.94/1.25  
% 1.94/1.25  %Foreground sorts:
% 1.94/1.25  
% 1.94/1.25  
% 1.94/1.25  %Background operators:
% 1.94/1.25  
% 1.94/1.25  
% 1.94/1.25  %Foreground operators:
% 1.94/1.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.25  
% 1.94/1.26  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_relat_1)).
% 1.94/1.26  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_relat_1)).
% 1.94/1.26  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_relat_1)).
% 1.94/1.26  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.94/1.26  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.26  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.26  tff(c_14, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.26  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.26  tff(c_4, plain, (![A_4, C_6, B_5]: (r1_tarski(k8_relat_1(A_4, C_6), k8_relat_1(B_5, C_6)) | ~r1_tarski(A_4, B_5) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.26  tff(c_48, plain, (![A_22, B_23, C_24]: (r1_tarski(k8_relat_1(A_22, B_23), k8_relat_1(A_22, C_24)) | ~r1_tarski(B_23, C_24) | ~v1_relat_1(C_24) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.26  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.26  tff(c_78, plain, (![A_33, A_34, C_35, B_36]: (r1_tarski(A_33, k8_relat_1(A_34, C_35)) | ~r1_tarski(A_33, k8_relat_1(A_34, B_36)) | ~r1_tarski(B_36, C_35) | ~v1_relat_1(C_35) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_48, c_2])).
% 1.94/1.26  tff(c_198, plain, (![A_56, C_57, B_58, C_59]: (r1_tarski(k8_relat_1(A_56, C_57), k8_relat_1(B_58, C_59)) | ~r1_tarski(C_57, C_59) | ~v1_relat_1(C_59) | ~r1_tarski(A_56, B_58) | ~v1_relat_1(C_57))), inference(resolution, [status(thm)], [c_4, c_78])).
% 1.94/1.26  tff(c_8, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.26  tff(c_215, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_198, c_8])).
% 1.94/1.26  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_10, c_14, c_12, c_215])).
% 1.94/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.26  
% 1.94/1.26  Inference rules
% 1.94/1.26  ----------------------
% 1.94/1.26  #Ref     : 0
% 1.94/1.26  #Sup     : 62
% 1.94/1.26  #Fact    : 0
% 1.94/1.26  #Define  : 0
% 1.94/1.26  #Split   : 2
% 1.94/1.26  #Chain   : 0
% 1.94/1.26  #Close   : 0
% 1.94/1.26  
% 1.94/1.26  Ordering : KBO
% 1.94/1.26  
% 1.94/1.26  Simplification rules
% 1.94/1.26  ----------------------
% 1.94/1.26  #Subsume      : 7
% 1.94/1.26  #Demod        : 5
% 1.94/1.26  #Tautology    : 1
% 1.94/1.26  #SimpNegUnit  : 0
% 1.94/1.26  #BackRed      : 0
% 1.94/1.26  
% 1.94/1.26  #Partial instantiations: 0
% 1.94/1.26  #Strategies tried      : 1
% 1.94/1.26  
% 1.94/1.26  Timing (in seconds)
% 1.94/1.26  ----------------------
% 1.94/1.26  Preprocessing        : 0.26
% 1.94/1.26  Parsing              : 0.15
% 1.94/1.26  CNF conversion       : 0.02
% 1.94/1.26  Main loop            : 0.24
% 1.94/1.26  Inferencing          : 0.09
% 1.94/1.26  Reduction            : 0.05
% 1.94/1.26  Demodulation         : 0.04
% 1.94/1.26  BG Simplification    : 0.01
% 1.94/1.26  Subsumption          : 0.07
% 1.94/1.26  Abstraction          : 0.01
% 1.94/1.26  MUC search           : 0.00
% 1.94/1.26  Cooper               : 0.00
% 1.94/1.26  Total                : 0.53
% 1.94/1.26  Index Insertion      : 0.00
% 1.94/1.26  Index Deletion       : 0.00
% 1.94/1.26  Index Matching       : 0.00
% 1.94/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
