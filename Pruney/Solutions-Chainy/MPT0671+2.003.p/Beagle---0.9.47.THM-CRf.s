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
% DateTime   : Thu Dec  3 10:04:20 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   28 (  41 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  66 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

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

tff(c_17,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_relat_1(A_12),k1_relat_1(B_13))
      | ~ r1_tarski(A_12,B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_17,c_10])).

tff(c_23,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_24,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_23])).

tff(c_27,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_24])).

tff(c_31,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_27])).

tff(c_32,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_23])).

tff(c_36,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_32])).

tff(c_40,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:29:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.34  
% 1.90/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.36  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.98/1.36  
% 1.98/1.36  %Foreground sorts:
% 1.98/1.36  
% 1.98/1.36  
% 1.98/1.36  %Background operators:
% 1.98/1.36  
% 1.98/1.36  
% 1.98/1.36  %Foreground operators:
% 1.98/1.36  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.98/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.36  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.36  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.36  
% 1.98/1.37  tff(f_51, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k1_relat_1(k8_relat_1(A, B)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_funct_1)).
% 1.98/1.37  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.98/1.37  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.98/1.37  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.98/1.37  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.37  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k8_relat_1(A_3, B_4), B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.37  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.37  tff(c_17, plain, (![A_12, B_13]: (r1_tarski(k1_relat_1(A_12), k1_relat_1(B_13)) | ~r1_tarski(A_12, B_13) | ~v1_relat_1(B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.37  tff(c_10, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.37  tff(c_20, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_17, c_10])).
% 1.98/1.37  tff(c_23, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 1.98/1.37  tff(c_24, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_23])).
% 1.98/1.37  tff(c_27, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_24])).
% 1.98/1.37  tff(c_31, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_27])).
% 1.98/1.37  tff(c_32, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_23])).
% 1.98/1.37  tff(c_36, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4, c_32])).
% 1.98/1.37  tff(c_40, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 1.98/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.37  
% 1.98/1.37  Inference rules
% 1.98/1.37  ----------------------
% 1.98/1.37  #Ref     : 0
% 1.98/1.37  #Sup     : 3
% 1.98/1.37  #Fact    : 0
% 1.98/1.37  #Define  : 0
% 1.98/1.37  #Split   : 1
% 1.98/1.37  #Chain   : 0
% 1.98/1.37  #Close   : 0
% 1.98/1.37  
% 1.98/1.37  Ordering : KBO
% 1.98/1.37  
% 1.98/1.37  Simplification rules
% 1.98/1.37  ----------------------
% 1.98/1.37  #Subsume      : 0
% 1.98/1.37  #Demod        : 3
% 1.98/1.37  #Tautology    : 0
% 1.98/1.37  #SimpNegUnit  : 0
% 1.98/1.37  #BackRed      : 0
% 1.98/1.37  
% 1.98/1.37  #Partial instantiations: 0
% 1.98/1.37  #Strategies tried      : 1
% 1.98/1.37  
% 1.98/1.37  Timing (in seconds)
% 1.98/1.37  ----------------------
% 1.98/1.38  Preprocessing        : 0.41
% 1.98/1.38  Parsing              : 0.22
% 1.98/1.38  CNF conversion       : 0.03
% 1.98/1.38  Main loop            : 0.14
% 1.98/1.38  Inferencing          : 0.05
% 1.98/1.38  Reduction            : 0.03
% 1.98/1.38  Demodulation         : 0.03
% 1.98/1.38  BG Simplification    : 0.01
% 1.98/1.38  Subsumption          : 0.02
% 1.98/1.38  Abstraction          : 0.01
% 1.98/1.38  MUC search           : 0.00
% 1.98/1.38  Cooper               : 0.00
% 1.98/1.38  Total                : 0.60
% 1.98/1.38  Index Insertion      : 0.00
% 1.98/1.38  Index Deletion       : 0.00
% 1.98/1.38  Index Matching       : 0.00
% 1.98/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
