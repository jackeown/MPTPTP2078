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
% DateTime   : Thu Dec  3 10:00:07 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   27 (  40 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  60 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k2_relat_1(k8_relat_1(A,B)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(k8_relat_1(A_3,B_4),B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k2_relat_1(A_14),k2_relat_1(B_15))
      | ~ r1_tarski(A_14,B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_19,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_10])).

tff(c_22,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_19])).

tff(c_23,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_26,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_23])).

tff(c_30,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_31,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_35,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_31])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.07  
% 1.51/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.08  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.51/1.08  
% 1.51/1.08  %Foreground sorts:
% 1.51/1.08  
% 1.51/1.08  
% 1.51/1.08  %Background operators:
% 1.51/1.08  
% 1.51/1.08  
% 1.51/1.08  %Foreground operators:
% 1.51/1.08  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.51/1.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.51/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.51/1.08  
% 1.63/1.09  tff(f_49, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_relat_1)).
% 1.63/1.09  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 1.63/1.09  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.63/1.09  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.63/1.09  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.63/1.09  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k8_relat_1(A_3, B_4), B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.63/1.09  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.09  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k2_relat_1(A_14), k2_relat_1(B_15)) | ~r1_tarski(A_14, B_15) | ~v1_relat_1(B_15) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.09  tff(c_10, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.63/1.09  tff(c_19, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_10])).
% 1.63/1.09  tff(c_22, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_19])).
% 1.63/1.09  tff(c_23, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_22])).
% 1.63/1.09  tff(c_26, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_23])).
% 1.63/1.09  tff(c_30, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 1.63/1.09  tff(c_31, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 1.63/1.09  tff(c_35, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4, c_31])).
% 1.63/1.09  tff(c_39, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_35])).
% 1.63/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  Inference rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Ref     : 0
% 1.63/1.09  #Sup     : 3
% 1.63/1.09  #Fact    : 0
% 1.63/1.09  #Define  : 0
% 1.63/1.09  #Split   : 1
% 1.63/1.09  #Chain   : 0
% 1.63/1.09  #Close   : 0
% 1.63/1.09  
% 1.63/1.09  Ordering : KBO
% 1.63/1.09  
% 1.63/1.09  Simplification rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Subsume      : 0
% 1.63/1.09  #Demod        : 3
% 1.63/1.09  #Tautology    : 0
% 1.63/1.09  #SimpNegUnit  : 0
% 1.63/1.09  #BackRed      : 0
% 1.63/1.09  
% 1.63/1.09  #Partial instantiations: 0
% 1.63/1.09  #Strategies tried      : 1
% 1.63/1.09  
% 1.63/1.09  Timing (in seconds)
% 1.63/1.09  ----------------------
% 1.63/1.09  Preprocessing        : 0.25
% 1.63/1.09  Parsing              : 0.14
% 1.63/1.09  CNF conversion       : 0.02
% 1.63/1.09  Main loop            : 0.08
% 1.63/1.09  Inferencing          : 0.03
% 1.63/1.09  Reduction            : 0.02
% 1.63/1.09  Demodulation         : 0.02
% 1.63/1.09  BG Simplification    : 0.01
% 1.63/1.09  Subsumption          : 0.01
% 1.63/1.09  Abstraction          : 0.00
% 1.63/1.09  MUC search           : 0.00
% 1.63/1.09  Cooper               : 0.00
% 1.63/1.09  Total                : 0.35
% 1.63/1.09  Index Insertion      : 0.00
% 1.63/1.09  Index Deletion       : 0.00
% 1.63/1.09  Index Matching       : 0.00
% 1.63/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
