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
% DateTime   : Thu Dec  3 09:59:56 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.24s
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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

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
    ! [C_6,A_4,B_5] :
      ( r1_tarski(k7_relat_1(C_6,A_4),k7_relat_1(C_6,B_5))
      | ~ r1_tarski(A_4,B_5)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    ! [B_22,A_23,C_24] :
      ( r1_tarski(k7_relat_1(B_22,A_23),k7_relat_1(C_24,A_23))
      | ~ r1_tarski(B_22,C_24)
      | ~ v1_relat_1(C_24)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_33,C_34,A_35,B_36] :
      ( r1_tarski(A_33,k7_relat_1(C_34,A_35))
      | ~ r1_tarski(A_33,k7_relat_1(B_36,A_35))
      | ~ r1_tarski(B_36,C_34)
      | ~ v1_relat_1(C_34)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_198,plain,(
    ! [C_56,A_57,C_58,B_59] :
      ( r1_tarski(k7_relat_1(C_56,A_57),k7_relat_1(C_58,B_59))
      | ~ r1_tarski(C_56,C_58)
      | ~ v1_relat_1(C_58)
      | ~ r1_tarski(A_57,B_59)
      | ~ v1_relat_1(C_56) ) ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_8,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.23  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.94/1.23  
% 1.94/1.23  %Foreground sorts:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Background operators:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Foreground operators:
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.94/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.23  
% 2.24/1.24  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 2.24/1.24  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_relat_1)).
% 2.24/1.24  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 2.24/1.24  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.24/1.24  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.24/1.24  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.24/1.24  tff(c_14, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.24/1.24  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.24/1.24  tff(c_4, plain, (![C_6, A_4, B_5]: (r1_tarski(k7_relat_1(C_6, A_4), k7_relat_1(C_6, B_5)) | ~r1_tarski(A_4, B_5) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.24  tff(c_48, plain, (![B_22, A_23, C_24]: (r1_tarski(k7_relat_1(B_22, A_23), k7_relat_1(C_24, A_23)) | ~r1_tarski(B_22, C_24) | ~v1_relat_1(C_24) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.24/1.24  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.24  tff(c_78, plain, (![A_33, C_34, A_35, B_36]: (r1_tarski(A_33, k7_relat_1(C_34, A_35)) | ~r1_tarski(A_33, k7_relat_1(B_36, A_35)) | ~r1_tarski(B_36, C_34) | ~v1_relat_1(C_34) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_48, c_2])).
% 2.24/1.24  tff(c_198, plain, (![C_56, A_57, C_58, B_59]: (r1_tarski(k7_relat_1(C_56, A_57), k7_relat_1(C_58, B_59)) | ~r1_tarski(C_56, C_58) | ~v1_relat_1(C_58) | ~r1_tarski(A_57, B_59) | ~v1_relat_1(C_56))), inference(resolution, [status(thm)], [c_4, c_78])).
% 2.24/1.24  tff(c_8, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.24/1.24  tff(c_215, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_198, c_8])).
% 2.24/1.24  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_10, c_14, c_12, c_215])).
% 2.24/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.24  
% 2.24/1.24  Inference rules
% 2.24/1.24  ----------------------
% 2.24/1.24  #Ref     : 0
% 2.24/1.24  #Sup     : 62
% 2.24/1.24  #Fact    : 0
% 2.24/1.24  #Define  : 0
% 2.24/1.24  #Split   : 2
% 2.24/1.24  #Chain   : 0
% 2.24/1.24  #Close   : 0
% 2.24/1.24  
% 2.24/1.24  Ordering : KBO
% 2.24/1.24  
% 2.24/1.24  Simplification rules
% 2.24/1.24  ----------------------
% 2.24/1.24  #Subsume      : 7
% 2.24/1.24  #Demod        : 5
% 2.24/1.24  #Tautology    : 1
% 2.24/1.24  #SimpNegUnit  : 0
% 2.24/1.24  #BackRed      : 0
% 2.24/1.24  
% 2.24/1.24  #Partial instantiations: 0
% 2.24/1.24  #Strategies tried      : 1
% 2.24/1.24  
% 2.24/1.24  Timing (in seconds)
% 2.24/1.24  ----------------------
% 2.24/1.24  Preprocessing        : 0.26
% 2.24/1.24  Parsing              : 0.15
% 2.24/1.24  CNF conversion       : 0.02
% 2.24/1.24  Main loop            : 0.23
% 2.24/1.24  Inferencing          : 0.09
% 2.24/1.24  Reduction            : 0.05
% 2.24/1.24  Demodulation         : 0.04
% 2.24/1.24  BG Simplification    : 0.01
% 2.24/1.24  Subsumption          : 0.07
% 2.24/1.24  Abstraction          : 0.01
% 2.24/1.24  MUC search           : 0.00
% 2.24/1.24  Cooper               : 0.00
% 2.24/1.24  Total                : 0.51
% 2.24/1.24  Index Insertion      : 0.00
% 2.24/1.24  Index Deletion       : 0.00
% 2.24/1.24  Index Matching       : 0.00
% 2.24/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
