%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:25 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   41 (  71 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 ( 100 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_241,plain,(
    ! [A_66,B_67] :
      ( k2_xboole_0(k2_relat_1(A_66),k2_relat_1(B_67)) = k2_relat_1(k2_xboole_0(A_66,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_292,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k2_relat_1(A_66),k2_relat_1(k2_xboole_0(A_66,B_67)))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_8])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k4_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_147,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(k4_xboole_0(A_43,B_44),C_45)
      | ~ r1_tarski(A_43,k2_xboole_0(B_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')),k2_relat_1(k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_27,plain,(
    ~ r1_tarski(k4_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')),k2_relat_1(k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_22])).

tff(c_151,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_xboole_0(k2_relat_1('#skF_2'),k2_relat_1(k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_147,c_27])).

tff(c_262,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_151])).

tff(c_304,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k2_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2,c_4,c_262])).

tff(c_319,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_322,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_319])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_322])).

tff(c_327,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_411,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_292,c_327])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.33  
% 2.62/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.33  %$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.62/1.33  
% 2.62/1.33  %Foreground sorts:
% 2.62/1.33  
% 2.62/1.33  
% 2.62/1.33  %Background operators:
% 2.62/1.33  
% 2.62/1.33  
% 2.62/1.33  %Foreground operators:
% 2.62/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.33  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.62/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.62/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.33  
% 2.62/1.34  tff(f_73, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 2.62/1.34  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 2.62/1.34  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.62/1.34  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.62/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.62/1.34  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.62/1.34  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.62/1.34  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.62/1.34  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.62/1.34  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.62/1.34  tff(c_241, plain, (![A_66, B_67]: (k2_xboole_0(k2_relat_1(A_66), k2_relat_1(B_67))=k2_relat_1(k2_xboole_0(A_66, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.62/1.34  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.34  tff(c_292, plain, (![A_66, B_67]: (r1_tarski(k2_relat_1(A_66), k2_relat_1(k2_xboole_0(A_66, B_67))) | ~v1_relat_1(B_67) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_241, c_8])).
% 2.62/1.34  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k4_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.62/1.34  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.62/1.34  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.34  tff(c_147, plain, (![A_43, B_44, C_45]: (r1_tarski(k4_xboole_0(A_43, B_44), C_45) | ~r1_tarski(A_43, k2_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.34  tff(c_10, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.34  tff(c_22, plain, (~r1_tarski(k6_subset_1(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')), k2_relat_1(k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.62/1.34  tff(c_27, plain, (~r1_tarski(k4_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')), k2_relat_1(k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_22])).
% 2.62/1.34  tff(c_151, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_xboole_0(k2_relat_1('#skF_2'), k2_relat_1(k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_147, c_27])).
% 2.62/1.34  tff(c_262, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_241, c_151])).
% 2.62/1.34  tff(c_304, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k2_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2, c_4, c_262])).
% 2.62/1.34  tff(c_319, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_304])).
% 2.62/1.34  tff(c_322, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_319])).
% 2.62/1.34  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_322])).
% 2.62/1.34  tff(c_327, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_304])).
% 2.62/1.34  tff(c_411, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_292, c_327])).
% 2.62/1.34  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_411])).
% 2.62/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.34  
% 2.62/1.34  Inference rules
% 2.62/1.34  ----------------------
% 2.62/1.34  #Ref     : 0
% 2.62/1.34  #Sup     : 104
% 2.62/1.34  #Fact    : 0
% 2.62/1.34  #Define  : 0
% 2.62/1.34  #Split   : 1
% 2.62/1.34  #Chain   : 0
% 2.62/1.34  #Close   : 0
% 2.62/1.34  
% 2.62/1.34  Ordering : KBO
% 2.62/1.34  
% 2.62/1.34  Simplification rules
% 2.62/1.34  ----------------------
% 2.62/1.34  #Subsume      : 8
% 2.62/1.34  #Demod        : 33
% 2.62/1.34  #Tautology    : 35
% 2.62/1.34  #SimpNegUnit  : 0
% 2.62/1.34  #BackRed      : 0
% 2.62/1.34  
% 2.62/1.34  #Partial instantiations: 0
% 2.62/1.34  #Strategies tried      : 1
% 2.62/1.34  
% 2.62/1.34  Timing (in seconds)
% 2.62/1.34  ----------------------
% 2.62/1.35  Preprocessing        : 0.30
% 2.62/1.35  Parsing              : 0.16
% 2.62/1.35  CNF conversion       : 0.02
% 2.62/1.35  Main loop            : 0.27
% 2.62/1.35  Inferencing          : 0.09
% 2.62/1.35  Reduction            : 0.09
% 2.62/1.35  Demodulation         : 0.08
% 2.62/1.35  BG Simplification    : 0.02
% 2.62/1.35  Subsumption          : 0.05
% 2.62/1.35  Abstraction          : 0.01
% 2.62/1.35  MUC search           : 0.00
% 2.62/1.35  Cooper               : 0.00
% 2.62/1.35  Total                : 0.60
% 2.62/1.35  Index Insertion      : 0.00
% 2.62/1.35  Index Deletion       : 0.00
% 2.62/1.35  Index Matching       : 0.00
% 2.62/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
