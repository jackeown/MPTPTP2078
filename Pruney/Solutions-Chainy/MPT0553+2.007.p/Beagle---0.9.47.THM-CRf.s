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
% DateTime   : Thu Dec  3 10:01:02 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   35 (  66 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 ( 130 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)),k9_relat_1(C,k6_subset_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( k6_subset_1(k7_relat_1(C_5,A_3),k7_relat_1(C_5,B_4)) = k7_relat_1(C_5,k6_subset_1(A_3,B_4))
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_15),k2_relat_1(B_16)),k2_relat_1(k6_subset_1(A_15,B_16)))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    ! [B_20,A_21,B_22] :
      ( r1_tarski(k6_subset_1(k9_relat_1(B_20,A_21),k2_relat_1(B_22)),k2_relat_1(k6_subset_1(k7_relat_1(B_20,A_21),B_22)))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k7_relat_1(B_20,A_21))
      | ~ v1_relat_1(B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_23])).

tff(c_81,plain,(
    ! [C_32,A_33,B_34] :
      ( r1_tarski(k6_subset_1(k9_relat_1(C_32,A_33),k2_relat_1(k7_relat_1(C_32,B_34))),k2_relat_1(k7_relat_1(C_32,k6_subset_1(A_33,B_34))))
      | ~ v1_relat_1(k7_relat_1(C_32,B_34))
      | ~ v1_relat_1(k7_relat_1(C_32,A_33))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_121,plain,(
    ! [B_48,A_49,B_50] :
      ( r1_tarski(k6_subset_1(k9_relat_1(B_48,A_49),k2_relat_1(k7_relat_1(B_48,B_50))),k9_relat_1(B_48,k6_subset_1(A_49,B_50)))
      | ~ v1_relat_1(k7_relat_1(B_48,B_50))
      | ~ v1_relat_1(k7_relat_1(B_48,A_49))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_81])).

tff(c_128,plain,(
    ! [B_51,A_52,A_53] :
      ( r1_tarski(k6_subset_1(k9_relat_1(B_51,A_52),k9_relat_1(B_51,A_53)),k9_relat_1(B_51,k6_subset_1(A_52,A_53)))
      | ~ v1_relat_1(k7_relat_1(B_51,A_53))
      | ~ v1_relat_1(k7_relat_1(B_51,A_52))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_121])).

tff(c_10,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')),k9_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_10])).

tff(c_137,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_131])).

tff(c_138,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_157,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_138])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_157])).

tff(c_162,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_166,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_162])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.22  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.03/1.22  
% 2.03/1.22  %Foreground sorts:
% 2.03/1.22  
% 2.03/1.22  
% 2.03/1.22  %Background operators:
% 2.03/1.22  
% 2.03/1.22  
% 2.03/1.22  %Foreground operators:
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.03/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.03/1.22  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.03/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.22  
% 2.16/1.23  tff(f_49, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)), k9_relat_1(C, k6_subset_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_relat_1)).
% 2.16/1.23  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.16/1.23  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.16/1.23  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 2.16/1.23  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 2.16/1.23  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.23  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.23  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.23  tff(c_4, plain, (![C_5, A_3, B_4]: (k6_subset_1(k7_relat_1(C_5, A_3), k7_relat_1(C_5, B_4))=k7_relat_1(C_5, k6_subset_1(A_3, B_4)) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.23  tff(c_23, plain, (![A_15, B_16]: (r1_tarski(k6_subset_1(k2_relat_1(A_15), k2_relat_1(B_16)), k2_relat_1(k6_subset_1(A_15, B_16))) | ~v1_relat_1(B_16) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.16/1.23  tff(c_42, plain, (![B_20, A_21, B_22]: (r1_tarski(k6_subset_1(k9_relat_1(B_20, A_21), k2_relat_1(B_22)), k2_relat_1(k6_subset_1(k7_relat_1(B_20, A_21), B_22))) | ~v1_relat_1(B_22) | ~v1_relat_1(k7_relat_1(B_20, A_21)) | ~v1_relat_1(B_20))), inference(superposition, [status(thm), theory('equality')], [c_6, c_23])).
% 2.16/1.23  tff(c_81, plain, (![C_32, A_33, B_34]: (r1_tarski(k6_subset_1(k9_relat_1(C_32, A_33), k2_relat_1(k7_relat_1(C_32, B_34))), k2_relat_1(k7_relat_1(C_32, k6_subset_1(A_33, B_34)))) | ~v1_relat_1(k7_relat_1(C_32, B_34)) | ~v1_relat_1(k7_relat_1(C_32, A_33)) | ~v1_relat_1(C_32) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_4, c_42])).
% 2.16/1.23  tff(c_121, plain, (![B_48, A_49, B_50]: (r1_tarski(k6_subset_1(k9_relat_1(B_48, A_49), k2_relat_1(k7_relat_1(B_48, B_50))), k9_relat_1(B_48, k6_subset_1(A_49, B_50))) | ~v1_relat_1(k7_relat_1(B_48, B_50)) | ~v1_relat_1(k7_relat_1(B_48, A_49)) | ~v1_relat_1(B_48) | ~v1_relat_1(B_48) | ~v1_relat_1(B_48))), inference(superposition, [status(thm), theory('equality')], [c_6, c_81])).
% 2.16/1.23  tff(c_128, plain, (![B_51, A_52, A_53]: (r1_tarski(k6_subset_1(k9_relat_1(B_51, A_52), k9_relat_1(B_51, A_53)), k9_relat_1(B_51, k6_subset_1(A_52, A_53))) | ~v1_relat_1(k7_relat_1(B_51, A_53)) | ~v1_relat_1(k7_relat_1(B_51, A_52)) | ~v1_relat_1(B_51) | ~v1_relat_1(B_51) | ~v1_relat_1(B_51) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_6, c_121])).
% 2.16/1.23  tff(c_10, plain, (~r1_tarski(k6_subset_1(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')), k9_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.23  tff(c_131, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_128, c_10])).
% 2.16/1.23  tff(c_137, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_131])).
% 2.16/1.23  tff(c_138, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_137])).
% 2.16/1.23  tff(c_157, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_138])).
% 2.16/1.23  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_157])).
% 2.16/1.23  tff(c_162, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_137])).
% 2.16/1.23  tff(c_166, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_162])).
% 2.16/1.23  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_166])).
% 2.16/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.23  
% 2.16/1.23  Inference rules
% 2.16/1.23  ----------------------
% 2.16/1.23  #Ref     : 0
% 2.16/1.23  #Sup     : 39
% 2.16/1.23  #Fact    : 0
% 2.16/1.23  #Define  : 0
% 2.16/1.23  #Split   : 1
% 2.16/1.23  #Chain   : 0
% 2.16/1.23  #Close   : 0
% 2.16/1.24  
% 2.16/1.24  Ordering : KBO
% 2.16/1.24  
% 2.16/1.24  Simplification rules
% 2.16/1.24  ----------------------
% 2.16/1.24  #Subsume      : 7
% 2.16/1.24  #Demod        : 3
% 2.16/1.24  #Tautology    : 4
% 2.16/1.24  #SimpNegUnit  : 0
% 2.16/1.24  #BackRed      : 0
% 2.16/1.24  
% 2.16/1.24  #Partial instantiations: 0
% 2.16/1.24  #Strategies tried      : 1
% 2.16/1.24  
% 2.16/1.24  Timing (in seconds)
% 2.16/1.24  ----------------------
% 2.16/1.24  Preprocessing        : 0.25
% 2.16/1.24  Parsing              : 0.14
% 2.16/1.24  CNF conversion       : 0.02
% 2.16/1.24  Main loop            : 0.23
% 2.16/1.24  Inferencing          : 0.10
% 2.16/1.24  Reduction            : 0.05
% 2.16/1.24  Demodulation         : 0.04
% 2.16/1.24  BG Simplification    : 0.01
% 2.16/1.24  Subsumption          : 0.05
% 2.16/1.24  Abstraction          : 0.01
% 2.16/1.24  MUC search           : 0.00
% 2.16/1.24  Cooper               : 0.00
% 2.16/1.24  Total                : 0.51
% 2.16/1.24  Index Insertion      : 0.00
% 2.16/1.24  Index Deletion       : 0.00
% 2.16/1.24  Index Matching       : 0.00
% 2.16/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
