%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:10 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   29 (  44 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  72 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(k7_relat_1(C,A),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k7_relat_1(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [C_21,A_22,D_23,B_24] :
      ( r1_tarski(k9_relat_1(C_21,A_22),k9_relat_1(D_23,B_24))
      | ~ r1_tarski(A_22,B_24)
      | ~ r1_tarski(C_21,D_23)
      | ~ v1_relat_1(D_23)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_35,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_14])).

tff(c_40,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6,c_35])).

tff(c_42,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_45,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_42])).

tff(c_49,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_45])).

tff(c_50,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_54,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_50])).

tff(c_58,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:27:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.18  
% 1.64/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.18  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.64/1.18  
% 1.64/1.18  %Foreground sorts:
% 1.64/1.18  
% 1.64/1.18  
% 1.64/1.18  %Background operators:
% 1.64/1.18  
% 1.64/1.18  
% 1.64/1.18  %Foreground operators:
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.64/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.64/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.18  
% 1.83/1.19  tff(f_55, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(k7_relat_1(C, A), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t161_relat_1)).
% 1.83/1.19  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.83/1.19  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.83/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.83/1.19  tff(f_46, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 1.83/1.19  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.19  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.83/1.19  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k7_relat_1(A_3, B_4)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.19  tff(c_32, plain, (![C_21, A_22, D_23, B_24]: (r1_tarski(k9_relat_1(C_21, A_22), k9_relat_1(D_23, B_24)) | ~r1_tarski(A_22, B_24) | ~r1_tarski(C_21, D_23) | ~v1_relat_1(D_23) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.83/1.19  tff(c_14, plain, (~r1_tarski(k9_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.19  tff(c_35, plain, (~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_14])).
% 1.83/1.19  tff(c_40, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_6, c_35])).
% 1.83/1.19  tff(c_42, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_40])).
% 1.83/1.19  tff(c_45, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_42])).
% 1.83/1.19  tff(c_49, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_45])).
% 1.83/1.19  tff(c_50, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 1.83/1.19  tff(c_54, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_50])).
% 1.83/1.19  tff(c_58, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_54])).
% 1.83/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  Inference rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Ref     : 0
% 1.83/1.19  #Sup     : 6
% 1.83/1.19  #Fact    : 0
% 1.83/1.19  #Define  : 0
% 1.83/1.19  #Split   : 1
% 1.83/1.19  #Chain   : 0
% 1.83/1.19  #Close   : 0
% 1.83/1.19  
% 1.83/1.19  Ordering : KBO
% 1.83/1.19  
% 1.83/1.19  Simplification rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Subsume      : 0
% 1.83/1.19  #Demod        : 6
% 1.83/1.19  #Tautology    : 2
% 1.83/1.19  #SimpNegUnit  : 0
% 1.83/1.19  #BackRed      : 0
% 1.83/1.19  
% 1.83/1.19  #Partial instantiations: 0
% 1.83/1.19  #Strategies tried      : 1
% 1.83/1.19  
% 1.83/1.19  Timing (in seconds)
% 1.83/1.19  ----------------------
% 1.83/1.19  Preprocessing        : 0.29
% 1.83/1.19  Parsing              : 0.16
% 1.83/1.19  CNF conversion       : 0.02
% 1.83/1.19  Main loop            : 0.11
% 1.83/1.19  Inferencing          : 0.05
% 1.83/1.19  Reduction            : 0.03
% 1.83/1.19  Demodulation         : 0.02
% 1.83/1.19  BG Simplification    : 0.01
% 1.83/1.19  Subsumption          : 0.02
% 1.83/1.19  Abstraction          : 0.00
% 1.83/1.19  MUC search           : 0.00
% 1.83/1.19  Cooper               : 0.00
% 1.83/1.20  Total                : 0.42
% 1.83/1.20  Index Insertion      : 0.00
% 1.83/1.20  Index Deletion       : 0.00
% 1.83/1.20  Index Matching       : 0.00
% 1.83/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
