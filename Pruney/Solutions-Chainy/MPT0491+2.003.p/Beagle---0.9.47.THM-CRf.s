%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:35 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
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
       => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

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

tff(c_15,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_relat_1(A_12),k1_relat_1(B_13))
      | ~ r1_tarski(A_12,B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_15,c_10])).

tff(c_21,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_23,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_21])).

tff(c_26,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_23])).

tff(c_30,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_31,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_21])).

tff(c_35,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.05  
% 1.53/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.06  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.53/1.06  
% 1.53/1.06  %Foreground sorts:
% 1.53/1.06  
% 1.53/1.06  
% 1.53/1.06  %Background operators:
% 1.53/1.06  
% 1.53/1.06  
% 1.53/1.06  %Foreground operators:
% 1.53/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.06  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.53/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.53/1.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.53/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.53/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.53/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.53/1.06  
% 1.53/1.07  tff(f_49, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 1.53/1.07  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.53/1.07  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.53/1.07  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.53/1.07  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.53/1.07  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k7_relat_1(B_7, A_6), B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.53/1.07  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.53/1.07  tff(c_15, plain, (![A_12, B_13]: (r1_tarski(k1_relat_1(A_12), k1_relat_1(B_13)) | ~r1_tarski(A_12, B_13) | ~v1_relat_1(B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.53/1.07  tff(c_10, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.53/1.07  tff(c_18, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_15, c_10])).
% 1.53/1.07  tff(c_21, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 1.53/1.07  tff(c_23, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_21])).
% 1.53/1.07  tff(c_26, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_23])).
% 1.53/1.07  tff(c_30, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 1.53/1.07  tff(c_31, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_21])).
% 1.53/1.07  tff(c_35, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_31])).
% 1.53/1.07  tff(c_39, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_35])).
% 1.53/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.07  
% 1.53/1.07  Inference rules
% 1.53/1.07  ----------------------
% 1.53/1.07  #Ref     : 0
% 1.53/1.07  #Sup     : 3
% 1.53/1.07  #Fact    : 0
% 1.53/1.07  #Define  : 0
% 1.53/1.07  #Split   : 1
% 1.53/1.07  #Chain   : 0
% 1.53/1.07  #Close   : 0
% 1.53/1.07  
% 1.53/1.07  Ordering : KBO
% 1.53/1.07  
% 1.53/1.07  Simplification rules
% 1.53/1.07  ----------------------
% 1.53/1.07  #Subsume      : 0
% 1.53/1.07  #Demod        : 3
% 1.53/1.07  #Tautology    : 0
% 1.53/1.07  #SimpNegUnit  : 0
% 1.53/1.07  #BackRed      : 0
% 1.53/1.07  
% 1.53/1.07  #Partial instantiations: 0
% 1.53/1.07  #Strategies tried      : 1
% 1.53/1.07  
% 1.53/1.07  Timing (in seconds)
% 1.53/1.07  ----------------------
% 1.53/1.07  Preprocessing        : 0.24
% 1.53/1.07  Parsing              : 0.13
% 1.53/1.07  CNF conversion       : 0.02
% 1.53/1.07  Main loop            : 0.07
% 1.53/1.07  Inferencing          : 0.03
% 1.53/1.07  Reduction            : 0.02
% 1.53/1.07  Demodulation         : 0.01
% 1.53/1.07  BG Simplification    : 0.01
% 1.53/1.07  Subsumption          : 0.01
% 1.53/1.07  Abstraction          : 0.00
% 1.53/1.07  MUC search           : 0.00
% 1.53/1.07  Cooper               : 0.00
% 1.53/1.07  Total                : 0.34
% 1.53/1.07  Index Insertion      : 0.00
% 1.53/1.07  Index Deletion       : 0.00
% 1.53/1.07  Index Matching       : 0.00
% 1.53/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
