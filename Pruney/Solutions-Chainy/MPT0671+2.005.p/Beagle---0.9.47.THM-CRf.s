%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:21 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   29 (  43 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  74 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k1_relat_1(k8_relat_1(A,B)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k8_relat_1(A_1,B_2),B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k1_relat_1(A_16),k1_relat_1(B_17))
      | ~ r1_tarski(A_16,B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_21,c_12])).

tff(c_27,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_28,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_27])).

tff(c_31,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_28])).

tff(c_35,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_31])).

tff(c_36,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_27])).

tff(c_40,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_36])).

tff(c_44,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.19  
% 1.62/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.20  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.62/1.20  
% 1.62/1.20  %Foreground sorts:
% 1.62/1.20  
% 1.62/1.20  
% 1.62/1.20  %Background operators:
% 1.62/1.20  
% 1.62/1.20  
% 1.62/1.20  %Foreground operators:
% 1.62/1.20  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.62/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.62/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.20  
% 1.62/1.21  tff(f_55, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k1_relat_1(k8_relat_1(A, B)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_funct_1)).
% 1.62/1.21  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 1.62/1.21  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_funct_1)).
% 1.62/1.21  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 1.62/1.21  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.62/1.21  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k8_relat_1(A_1, B_2), B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.21  tff(c_14, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.62/1.21  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.62/1.21  tff(c_21, plain, (![A_16, B_17]: (r1_tarski(k1_relat_1(A_16), k1_relat_1(B_17)) | ~r1_tarski(A_16, B_17) | ~v1_relat_1(B_17) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.21  tff(c_12, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.62/1.21  tff(c_24, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_21, c_12])).
% 1.62/1.21  tff(c_27, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 1.62/1.21  tff(c_28, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_27])).
% 1.62/1.21  tff(c_31, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_28])).
% 1.62/1.21  tff(c_35, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_31])).
% 1.62/1.21  tff(c_36, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_27])).
% 1.62/1.21  tff(c_40, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_36])).
% 1.62/1.21  tff(c_44, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_40])).
% 1.62/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.21  
% 1.62/1.21  Inference rules
% 1.62/1.21  ----------------------
% 1.62/1.21  #Ref     : 0
% 1.62/1.21  #Sup     : 3
% 1.62/1.21  #Fact    : 0
% 1.62/1.21  #Define  : 0
% 1.62/1.21  #Split   : 1
% 1.62/1.21  #Chain   : 0
% 1.62/1.21  #Close   : 0
% 1.62/1.21  
% 1.62/1.21  Ordering : KBO
% 1.62/1.21  
% 1.62/1.21  Simplification rules
% 1.62/1.21  ----------------------
% 1.62/1.21  #Subsume      : 0
% 1.62/1.21  #Demod        : 4
% 1.62/1.21  #Tautology    : 0
% 1.62/1.21  #SimpNegUnit  : 0
% 1.62/1.21  #BackRed      : 0
% 1.62/1.21  
% 1.62/1.21  #Partial instantiations: 0
% 1.62/1.21  #Strategies tried      : 1
% 1.62/1.21  
% 1.62/1.21  Timing (in seconds)
% 1.62/1.21  ----------------------
% 1.62/1.21  Preprocessing        : 0.24
% 1.62/1.21  Parsing              : 0.13
% 1.62/1.21  CNF conversion       : 0.02
% 1.62/1.21  Main loop            : 0.09
% 1.62/1.21  Inferencing          : 0.04
% 1.62/1.21  Reduction            : 0.02
% 1.62/1.21  Demodulation         : 0.02
% 1.62/1.21  BG Simplification    : 0.01
% 1.62/1.22  Subsumption          : 0.01
% 1.62/1.22  Abstraction          : 0.00
% 1.62/1.22  MUC search           : 0.00
% 1.62/1.22  Cooper               : 0.00
% 1.62/1.22  Total                : 0.36
% 1.62/1.22  Index Insertion      : 0.00
% 1.62/1.22  Index Deletion       : 0.00
% 1.62/1.22  Index Matching       : 0.00
% 1.62/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
