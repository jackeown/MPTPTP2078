%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:06 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   39 (  87 expanded)
%              Number of leaves         :   17 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 209 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [B_4,A_3,C_6] :
      ( r1_tarski(k7_relat_1(B_4,A_3),k7_relat_1(C_6,A_3))
      | ~ r1_tarski(B_4,C_6)
      | ~ v1_relat_1(C_6)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k2_relat_1(A_19),k2_relat_1(B_20))
      | ~ r1_tarski(A_19,B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_24,B_25,A_26] :
      ( r1_tarski(k2_relat_1(A_24),k9_relat_1(B_25,A_26))
      | ~ r1_tarski(A_24,k7_relat_1(B_25,A_26))
      | ~ v1_relat_1(k7_relat_1(B_25,A_26))
      | ~ v1_relat_1(A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_30])).

tff(c_46,plain,(
    ! [B_30,A_31,B_32,A_33] :
      ( r1_tarski(k9_relat_1(B_30,A_31),k9_relat_1(B_32,A_33))
      | ~ r1_tarski(k7_relat_1(B_30,A_31),k7_relat_1(B_32,A_33))
      | ~ v1_relat_1(k7_relat_1(B_32,A_33))
      | ~ v1_relat_1(k7_relat_1(B_30,A_31))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_38])).

tff(c_12,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_49,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_12])).

tff(c_52,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_49])).

tff(c_53,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_53])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_56])).

tff(c_61,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_63,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_66,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_63])).

tff(c_70,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_66])).

tff(c_71,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_75,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.21  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.81/1.21  
% 1.81/1.21  %Foreground sorts:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Background operators:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Foreground operators:
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.81/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.81/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.21  
% 1.81/1.22  tff(f_63, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 1.81/1.22  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.81/1.22  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 1.81/1.22  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.81/1.22  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.81/1.22  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.81/1.22  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.22  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.81/1.22  tff(c_14, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.81/1.22  tff(c_4, plain, (![B_4, A_3, C_6]: (r1_tarski(k7_relat_1(B_4, A_3), k7_relat_1(C_6, A_3)) | ~r1_tarski(B_4, C_6) | ~v1_relat_1(C_6) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.81/1.22  tff(c_6, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.22  tff(c_30, plain, (![A_19, B_20]: (r1_tarski(k2_relat_1(A_19), k2_relat_1(B_20)) | ~r1_tarski(A_19, B_20) | ~v1_relat_1(B_20) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.81/1.22  tff(c_38, plain, (![A_24, B_25, A_26]: (r1_tarski(k2_relat_1(A_24), k9_relat_1(B_25, A_26)) | ~r1_tarski(A_24, k7_relat_1(B_25, A_26)) | ~v1_relat_1(k7_relat_1(B_25, A_26)) | ~v1_relat_1(A_24) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_6, c_30])).
% 1.81/1.22  tff(c_46, plain, (![B_30, A_31, B_32, A_33]: (r1_tarski(k9_relat_1(B_30, A_31), k9_relat_1(B_32, A_33)) | ~r1_tarski(k7_relat_1(B_30, A_31), k7_relat_1(B_32, A_33)) | ~v1_relat_1(k7_relat_1(B_32, A_33)) | ~v1_relat_1(k7_relat_1(B_30, A_31)) | ~v1_relat_1(B_32) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_6, c_38])).
% 1.81/1.22  tff(c_12, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.81/1.22  tff(c_49, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_12])).
% 1.81/1.22  tff(c_52, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_49])).
% 1.81/1.22  tff(c_53, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 1.81/1.22  tff(c_56, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_53])).
% 1.81/1.22  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_56])).
% 1.81/1.22  tff(c_61, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_52])).
% 1.81/1.22  tff(c_63, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_61])).
% 1.81/1.22  tff(c_66, plain, (~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4, c_63])).
% 1.81/1.22  tff(c_70, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_14, c_66])).
% 1.81/1.22  tff(c_71, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_61])).
% 1.81/1.22  tff(c_75, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_71])).
% 1.81/1.22  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_75])).
% 1.81/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  Inference rules
% 1.81/1.22  ----------------------
% 1.81/1.22  #Ref     : 0
% 1.81/1.22  #Sup     : 10
% 1.81/1.22  #Fact    : 0
% 1.81/1.22  #Define  : 0
% 1.81/1.22  #Split   : 2
% 1.81/1.22  #Chain   : 0
% 1.81/1.22  #Close   : 0
% 1.81/1.22  
% 1.81/1.22  Ordering : KBO
% 1.81/1.22  
% 1.81/1.22  Simplification rules
% 1.81/1.22  ----------------------
% 1.81/1.22  #Subsume      : 1
% 1.81/1.22  #Demod        : 7
% 1.81/1.22  #Tautology    : 2
% 1.81/1.22  #SimpNegUnit  : 0
% 1.81/1.22  #BackRed      : 0
% 1.81/1.22  
% 1.81/1.22  #Partial instantiations: 0
% 1.81/1.22  #Strategies tried      : 1
% 1.81/1.22  
% 1.81/1.22  Timing (in seconds)
% 1.81/1.22  ----------------------
% 1.81/1.22  Preprocessing        : 0.28
% 1.81/1.22  Parsing              : 0.16
% 1.81/1.22  CNF conversion       : 0.02
% 1.81/1.22  Main loop            : 0.13
% 1.81/1.22  Inferencing          : 0.06
% 1.81/1.22  Reduction            : 0.03
% 1.81/1.22  Demodulation         : 0.02
% 1.81/1.22  BG Simplification    : 0.01
% 1.81/1.22  Subsumption          : 0.02
% 1.81/1.22  Abstraction          : 0.00
% 1.81/1.22  MUC search           : 0.00
% 1.81/1.22  Cooper               : 0.00
% 1.81/1.22  Total                : 0.44
% 1.81/1.22  Index Insertion      : 0.00
% 1.81/1.22  Index Deletion       : 0.00
% 1.81/1.22  Index Matching       : 0.00
% 1.81/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
