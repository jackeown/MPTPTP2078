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
% DateTime   : Thu Dec  3 09:58:17 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   42 (  70 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 ( 104 expanded)
%              Number of equality atoms :    7 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(k1_relat_1(A_45),k1_relat_1(B_46)) = k1_relat_1(k2_xboole_0(A_45,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_200,plain,(
    ! [A_59,A_60,B_61] :
      ( r1_tarski(A_59,k1_relat_1(k2_xboole_0(A_60,B_61)))
      | ~ r1_tarski(A_59,k1_relat_1(B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_8])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k4_xboole_0(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    ! [A_35,B_36,C_37] :
      ( r1_tarski(k4_xboole_0(A_35,B_36),C_37)
      | ~ r1_tarski(A_35,k2_xboole_0(B_36,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_27,plain,(
    ~ r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')),k1_relat_1(k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_22])).

tff(c_78,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k2_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_72,c_27])).

tff(c_115,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_78])).

tff(c_130,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_2','#skF_1')))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10,c_115])).

tff(c_132,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_135,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_132])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_135])).

tff(c_140,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(k2_xboole_0('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_207,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_200,c_140])).

tff(c_220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_6,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n011.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 17:45:57 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.29  
% 2.14/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.29  %$ r1_tarski > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_relat_1 > #skF_2 > #skF_1
% 2.14/1.29  
% 2.14/1.29  %Foreground sorts:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Background operators:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Foreground operators:
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.29  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.14/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.14/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.29  
% 2.14/1.30  tff(f_64, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 2.14/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.14/1.30  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 2.14/1.30  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.14/1.30  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.14/1.30  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.14/1.30  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.14/1.30  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.14/1.30  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.30  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.30  tff(c_109, plain, (![A_45, B_46]: (k2_xboole_0(k1_relat_1(A_45), k1_relat_1(B_46))=k1_relat_1(k2_xboole_0(A_45, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.30  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.30  tff(c_200, plain, (![A_59, A_60, B_61]: (r1_tarski(A_59, k1_relat_1(k2_xboole_0(A_60, B_61))) | ~r1_tarski(A_59, k1_relat_1(B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(A_60))), inference(superposition, [status(thm), theory('equality')], [c_109, c_8])).
% 2.14/1.30  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k4_xboole_0(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.30  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.30  tff(c_72, plain, (![A_35, B_36, C_37]: (r1_tarski(k4_xboole_0(A_35, B_36), C_37) | ~r1_tarski(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.30  tff(c_16, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.30  tff(c_22, plain, (~r1_tarski(k6_subset_1(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.30  tff(c_27, plain, (~r1_tarski(k4_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_22])).
% 2.14/1.30  tff(c_78, plain, (~r1_tarski(k1_relat_1('#skF_1'), k2_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_72, c_27])).
% 2.14/1.30  tff(c_115, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_109, c_78])).
% 2.14/1.30  tff(c_130, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_2', '#skF_1'))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_10, c_115])).
% 2.14/1.30  tff(c_132, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_130])).
% 2.14/1.30  tff(c_135, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_132])).
% 2.14/1.30  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_135])).
% 2.14/1.30  tff(c_140, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(k2_xboole_0('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_130])).
% 2.14/1.30  tff(c_207, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_200, c_140])).
% 2.14/1.30  tff(c_220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_6, c_207])).
% 2.14/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  Inference rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Ref     : 0
% 2.14/1.30  #Sup     : 44
% 2.14/1.30  #Fact    : 0
% 2.14/1.30  #Define  : 0
% 2.14/1.30  #Split   : 1
% 2.14/1.30  #Chain   : 0
% 2.14/1.30  #Close   : 0
% 2.14/1.30  
% 2.14/1.30  Ordering : KBO
% 2.14/1.30  
% 2.14/1.30  Simplification rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Subsume      : 0
% 2.14/1.30  #Demod        : 13
% 2.14/1.30  #Tautology    : 12
% 2.14/1.30  #SimpNegUnit  : 0
% 2.14/1.30  #BackRed      : 0
% 2.14/1.30  
% 2.14/1.30  #Partial instantiations: 0
% 2.14/1.30  #Strategies tried      : 1
% 2.14/1.30  
% 2.14/1.30  Timing (in seconds)
% 2.14/1.30  ----------------------
% 2.14/1.30  Preprocessing        : 0.33
% 2.14/1.30  Parsing              : 0.17
% 2.14/1.30  CNF conversion       : 0.02
% 2.14/1.30  Main loop            : 0.18
% 2.14/1.30  Inferencing          : 0.07
% 2.14/1.30  Reduction            : 0.05
% 2.14/1.30  Demodulation         : 0.04
% 2.14/1.30  BG Simplification    : 0.01
% 2.14/1.30  Subsumption          : 0.04
% 2.14/1.30  Abstraction          : 0.01
% 2.14/1.30  MUC search           : 0.00
% 2.14/1.30  Cooper               : 0.00
% 2.14/1.30  Total                : 0.54
% 2.14/1.30  Index Insertion      : 0.00
% 2.14/1.30  Index Deletion       : 0.00
% 2.14/1.30  Index Matching       : 0.00
% 2.14/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
