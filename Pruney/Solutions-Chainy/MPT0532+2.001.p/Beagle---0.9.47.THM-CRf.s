%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:16 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   30 (  37 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  81 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( v1_relat_1(D)
                 => ( ( r1_tarski(A,B)
                      & r1_tarski(C,D) )
                   => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = k8_relat_1(A_4,B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    ! [A_28,C_29,B_30,D_31] :
      ( r1_tarski(k5_relat_1(A_28,C_29),k5_relat_1(B_30,D_31))
      | ~ r1_tarski(C_29,D_31)
      | ~ r1_tarski(A_28,B_30)
      | ~ v1_relat_1(D_31)
      | ~ v1_relat_1(C_29)
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_49,plain,(
    ! [A_4,B_5,B_30,D_31] :
      ( r1_tarski(k8_relat_1(A_4,B_5),k5_relat_1(B_30,D_31))
      | ~ r1_tarski(k6_relat_1(A_4),D_31)
      | ~ r1_tarski(B_5,B_30)
      | ~ v1_relat_1(D_31)
      | ~ v1_relat_1(k6_relat_1(A_4))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_58,plain,(
    ! [A_32,B_33,B_34,D_35] :
      ( r1_tarski(k8_relat_1(A_32,B_33),k5_relat_1(B_34,D_35))
      | ~ r1_tarski(k6_relat_1(A_32),D_35)
      | ~ r1_tarski(B_33,B_34)
      | ~ v1_relat_1(D_35)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_49])).

tff(c_63,plain,(
    ! [A_32,B_33,A_4,B_5] :
      ( r1_tarski(k8_relat_1(A_32,B_33),k8_relat_1(A_4,B_5))
      | ~ r1_tarski(k6_relat_1(A_32),k6_relat_1(A_4))
      | ~ r1_tarski(B_33,B_5)
      | ~ v1_relat_1(k6_relat_1(A_4))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_67,plain,(
    ! [A_36,B_37,A_38,B_39] :
      ( r1_tarski(k8_relat_1(A_36,B_37),k8_relat_1(A_38,B_39))
      | ~ r1_tarski(k6_relat_1(A_36),k6_relat_1(A_38))
      | ~ r1_tarski(B_37,B_39)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_14,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),k8_relat_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,
    ( ~ r1_tarski(k6_relat_1('#skF_1'),k6_relat_1('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_14])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_16,c_6,c_72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:14:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.11  
% 1.75/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.12  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.75/1.12  
% 1.75/1.12  %Foreground sorts:
% 1.75/1.12  
% 1.75/1.12  
% 1.75/1.12  %Background operators:
% 1.75/1.12  
% 1.75/1.12  
% 1.75/1.12  %Foreground operators:
% 1.75/1.12  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.75/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.12  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.75/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.75/1.12  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.75/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.12  
% 1.75/1.13  tff(f_64, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 1.75/1.13  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.75/1.13  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.75/1.13  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.75/1.13  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 1.75/1.13  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.75/1.13  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.75/1.13  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.75/1.13  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.75/1.13  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.13  tff(c_10, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=k8_relat_1(A_4, B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.13  tff(c_44, plain, (![A_28, C_29, B_30, D_31]: (r1_tarski(k5_relat_1(A_28, C_29), k5_relat_1(B_30, D_31)) | ~r1_tarski(C_29, D_31) | ~r1_tarski(A_28, B_30) | ~v1_relat_1(D_31) | ~v1_relat_1(C_29) | ~v1_relat_1(B_30) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.75/1.13  tff(c_49, plain, (![A_4, B_5, B_30, D_31]: (r1_tarski(k8_relat_1(A_4, B_5), k5_relat_1(B_30, D_31)) | ~r1_tarski(k6_relat_1(A_4), D_31) | ~r1_tarski(B_5, B_30) | ~v1_relat_1(D_31) | ~v1_relat_1(k6_relat_1(A_4)) | ~v1_relat_1(B_30) | ~v1_relat_1(B_5) | ~v1_relat_1(B_5))), inference(superposition, [status(thm), theory('equality')], [c_10, c_44])).
% 1.75/1.13  tff(c_58, plain, (![A_32, B_33, B_34, D_35]: (r1_tarski(k8_relat_1(A_32, B_33), k5_relat_1(B_34, D_35)) | ~r1_tarski(k6_relat_1(A_32), D_35) | ~r1_tarski(B_33, B_34) | ~v1_relat_1(D_35) | ~v1_relat_1(B_34) | ~v1_relat_1(B_33))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_49])).
% 1.75/1.13  tff(c_63, plain, (![A_32, B_33, A_4, B_5]: (r1_tarski(k8_relat_1(A_32, B_33), k8_relat_1(A_4, B_5)) | ~r1_tarski(k6_relat_1(A_32), k6_relat_1(A_4)) | ~r1_tarski(B_33, B_5) | ~v1_relat_1(k6_relat_1(A_4)) | ~v1_relat_1(B_5) | ~v1_relat_1(B_33) | ~v1_relat_1(B_5))), inference(superposition, [status(thm), theory('equality')], [c_10, c_58])).
% 1.75/1.13  tff(c_67, plain, (![A_36, B_37, A_38, B_39]: (r1_tarski(k8_relat_1(A_36, B_37), k8_relat_1(A_38, B_39)) | ~r1_tarski(k6_relat_1(A_36), k6_relat_1(A_38)) | ~r1_tarski(B_37, B_39) | ~v1_relat_1(B_37) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_63])).
% 1.75/1.13  tff(c_14, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), k8_relat_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.75/1.13  tff(c_72, plain, (~r1_tarski(k6_relat_1('#skF_1'), k6_relat_1('#skF_1')) | ~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_67, c_14])).
% 1.75/1.13  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_16, c_6, c_72])).
% 1.75/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.13  
% 1.75/1.13  Inference rules
% 1.75/1.13  ----------------------
% 1.75/1.13  #Ref     : 0
% 1.75/1.13  #Sup     : 11
% 1.75/1.13  #Fact    : 0
% 1.75/1.13  #Define  : 0
% 1.75/1.13  #Split   : 1
% 1.75/1.13  #Chain   : 0
% 1.75/1.13  #Close   : 0
% 1.75/1.13  
% 1.75/1.13  Ordering : KBO
% 1.75/1.13  
% 1.75/1.13  Simplification rules
% 1.75/1.13  ----------------------
% 1.75/1.13  #Subsume      : 0
% 1.75/1.13  #Demod        : 9
% 1.75/1.13  #Tautology    : 4
% 1.75/1.13  #SimpNegUnit  : 0
% 1.75/1.13  #BackRed      : 0
% 1.75/1.13  
% 1.75/1.13  #Partial instantiations: 0
% 1.75/1.13  #Strategies tried      : 1
% 1.75/1.13  
% 1.75/1.13  Timing (in seconds)
% 1.75/1.13  ----------------------
% 1.75/1.13  Preprocessing        : 0.26
% 1.75/1.13  Parsing              : 0.15
% 1.75/1.13  CNF conversion       : 0.02
% 1.75/1.13  Main loop            : 0.12
% 1.75/1.13  Inferencing          : 0.05
% 1.75/1.13  Reduction            : 0.03
% 1.75/1.13  Demodulation         : 0.03
% 1.75/1.13  BG Simplification    : 0.01
% 1.75/1.13  Subsumption          : 0.03
% 1.75/1.13  Abstraction          : 0.01
% 1.75/1.13  MUC search           : 0.00
% 1.75/1.13  Cooper               : 0.00
% 1.75/1.13  Total                : 0.40
% 1.75/1.13  Index Insertion      : 0.00
% 1.75/1.13  Index Deletion       : 0.00
% 1.75/1.13  Index Matching       : 0.00
% 1.75/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
