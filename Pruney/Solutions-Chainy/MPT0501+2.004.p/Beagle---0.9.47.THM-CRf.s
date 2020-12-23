%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:48 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 2.00s
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
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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
       => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_40,axiom,(
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

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k7_relat_1(B_7,A_6),B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k2_relat_1(A_14),k2_relat_1(B_15))
      | ~ r1_tarski(A_14,B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2','#skF_1')),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_19,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_10])).

tff(c_22,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_19])).

tff(c_23,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_26,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_23])).

tff(c_30,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_31,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_35,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.43  
% 1.84/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.44  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.84/1.44  
% 1.84/1.44  %Foreground sorts:
% 1.84/1.44  
% 1.84/1.44  
% 1.84/1.44  %Background operators:
% 1.84/1.44  
% 1.84/1.44  
% 1.84/1.44  %Foreground operators:
% 1.84/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.84/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.84/1.44  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.44  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.84/1.44  
% 1.84/1.46  tff(f_49, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 1.84/1.46  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.84/1.46  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.84/1.46  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.84/1.46  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.46  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k7_relat_1(B_7, A_6), B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.46  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.46  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k2_relat_1(A_14), k2_relat_1(B_15)) | ~r1_tarski(A_14, B_15) | ~v1_relat_1(B_15) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.00/1.46  tff(c_10, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', '#skF_1')), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.00/1.46  tff(c_19, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_10])).
% 2.00/1.46  tff(c_22, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_19])).
% 2.00/1.46  tff(c_23, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_22])).
% 2.00/1.46  tff(c_26, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_23])).
% 2.00/1.46  tff(c_30, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 2.00/1.46  tff(c_31, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 2.00/1.46  tff(c_35, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_31])).
% 2.00/1.46  tff(c_39, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_35])).
% 2.00/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.46  
% 2.00/1.46  Inference rules
% 2.00/1.46  ----------------------
% 2.00/1.46  #Ref     : 0
% 2.00/1.46  #Sup     : 3
% 2.00/1.46  #Fact    : 0
% 2.00/1.46  #Define  : 0
% 2.00/1.46  #Split   : 1
% 2.00/1.46  #Chain   : 0
% 2.00/1.46  #Close   : 0
% 2.00/1.46  
% 2.00/1.46  Ordering : KBO
% 2.00/1.46  
% 2.00/1.46  Simplification rules
% 2.00/1.46  ----------------------
% 2.00/1.46  #Subsume      : 0
% 2.00/1.46  #Demod        : 3
% 2.00/1.46  #Tautology    : 0
% 2.00/1.46  #SimpNegUnit  : 0
% 2.00/1.46  #BackRed      : 0
% 2.00/1.46  
% 2.00/1.46  #Partial instantiations: 0
% 2.00/1.46  #Strategies tried      : 1
% 2.00/1.46  
% 2.00/1.46  Timing (in seconds)
% 2.00/1.46  ----------------------
% 2.00/1.46  Preprocessing        : 0.39
% 2.00/1.46  Parsing              : 0.21
% 2.00/1.46  CNF conversion       : 0.03
% 2.00/1.46  Main loop            : 0.14
% 2.00/1.46  Inferencing          : 0.06
% 2.00/1.46  Reduction            : 0.03
% 2.00/1.47  Demodulation         : 0.03
% 2.00/1.47  BG Simplification    : 0.01
% 2.00/1.47  Subsumption          : 0.02
% 2.00/1.47  Abstraction          : 0.01
% 2.00/1.47  MUC search           : 0.00
% 2.00/1.47  Cooper               : 0.00
% 2.00/1.47  Total                : 0.58
% 2.00/1.47  Index Insertion      : 0.00
% 2.00/1.47  Index Deletion       : 0.00
% 2.00/1.47  Index Matching       : 0.00
% 2.00/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
