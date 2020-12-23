%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:48 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   46 (  78 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 ( 136 expanded)
%              Number of equality atoms :    8 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k6_subset_1(k5_relat_1(A,B),k5_relat_1(A,C)),k5_relat_1(A,k6_subset_1(B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(A,k2_xboole_0(B,C)) = k2_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_53,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_263,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_xboole_0(k5_relat_1(A_69,B_70),k5_relat_1(A_69,C_71)) = k5_relat_1(A_69,k2_xboole_0(B_70,C_71))
      | ~ v1_relat_1(C_71)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_617,plain,(
    ! [A_107,A_108,B_109,C_110] :
      ( r1_tarski(A_107,k5_relat_1(A_108,k2_xboole_0(B_109,C_110)))
      | ~ r1_tarski(A_107,k5_relat_1(A_108,C_110))
      | ~ v1_relat_1(C_110)
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_8])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k4_xboole_0(A_19,B_20))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [A_21,B_25,C_27] :
      ( k2_xboole_0(k5_relat_1(A_21,B_25),k5_relat_1(A_21,C_27)) = k5_relat_1(A_21,k2_xboole_0(B_25,C_27))
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_202,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(k4_xboole_0(A_57,B_58),C_59)
      | ~ r1_tarski(A_57,k2_xboole_0(B_58,C_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_17,B_18] : k6_subset_1(A_17,B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3')),k5_relat_1('#skF_1',k6_subset_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_33,plain,(
    ~ r1_tarski(k4_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3')),k5_relat_1('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_26])).

tff(c_209,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k2_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_202,c_33])).

tff(c_336,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_209])).

tff(c_344,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_10,c_336])).

tff(c_447,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_450,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_447])).

tff(c_454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_450])).

tff(c_455,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_632,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_617,c_455])).

tff(c_657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_30,c_6,c_632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:23:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  
% 2.77/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 2.77/1.38  
% 2.77/1.38  %Foreground sorts:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Background operators:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Foreground operators:
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.77/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.38  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.77/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.77/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.38  
% 2.77/1.39  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k5_relat_1(A, B), k5_relat_1(A, C)), k5_relat_1(A, k6_subset_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relat_1)).
% 2.77/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.77/1.39  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(A, k2_xboole_0(B, C)) = k2_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_relat_1)).
% 2.77/1.39  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.77/1.39  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.77/1.39  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.77/1.39  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.77/1.39  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.77/1.39  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.39  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.39  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.39  tff(c_263, plain, (![A_69, B_70, C_71]: (k2_xboole_0(k5_relat_1(A_69, B_70), k5_relat_1(A_69, C_71))=k5_relat_1(A_69, k2_xboole_0(B_70, C_71)) | ~v1_relat_1(C_71) | ~v1_relat_1(B_70) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.77/1.39  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.39  tff(c_617, plain, (![A_107, A_108, B_109, C_110]: (r1_tarski(A_107, k5_relat_1(A_108, k2_xboole_0(B_109, C_110))) | ~r1_tarski(A_107, k5_relat_1(A_108, C_110)) | ~v1_relat_1(C_110) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(superposition, [status(thm), theory('equality')], [c_263, c_8])).
% 2.77/1.39  tff(c_22, plain, (![A_19, B_20]: (v1_relat_1(k4_xboole_0(A_19, B_20)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.77/1.39  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.39  tff(c_24, plain, (![A_21, B_25, C_27]: (k2_xboole_0(k5_relat_1(A_21, B_25), k5_relat_1(A_21, C_27))=k5_relat_1(A_21, k2_xboole_0(B_25, C_27)) | ~v1_relat_1(C_27) | ~v1_relat_1(B_25) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.77/1.39  tff(c_202, plain, (![A_57, B_58, C_59]: (r1_tarski(k4_xboole_0(A_57, B_58), C_59) | ~r1_tarski(A_57, k2_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.77/1.39  tff(c_20, plain, (![A_17, B_18]: (k6_subset_1(A_17, B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.39  tff(c_26, plain, (~r1_tarski(k6_subset_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')), k5_relat_1('#skF_1', k6_subset_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.39  tff(c_33, plain, (~r1_tarski(k4_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')), k5_relat_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_26])).
% 2.77/1.39  tff(c_209, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k2_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_202, c_33])).
% 2.77/1.39  tff(c_336, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3')))) | ~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_209])).
% 2.77/1.39  tff(c_344, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_10, c_336])).
% 2.77/1.39  tff(c_447, plain, (~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_344])).
% 2.77/1.39  tff(c_450, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_447])).
% 2.77/1.39  tff(c_454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_450])).
% 2.77/1.39  tff(c_455, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_344])).
% 2.77/1.39  tff(c_632, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_617, c_455])).
% 2.77/1.39  tff(c_657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_30, c_6, c_632])).
% 2.77/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.39  
% 2.77/1.39  Inference rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Ref     : 0
% 2.77/1.40  #Sup     : 159
% 2.77/1.40  #Fact    : 0
% 2.77/1.40  #Define  : 0
% 2.77/1.40  #Split   : 1
% 2.77/1.40  #Chain   : 0
% 2.77/1.40  #Close   : 0
% 2.77/1.40  
% 2.77/1.40  Ordering : KBO
% 2.77/1.40  
% 2.77/1.40  Simplification rules
% 2.77/1.40  ----------------------
% 2.77/1.40  #Subsume      : 17
% 2.77/1.40  #Demod        : 41
% 2.77/1.40  #Tautology    : 51
% 2.77/1.40  #SimpNegUnit  : 0
% 2.77/1.40  #BackRed      : 0
% 2.77/1.40  
% 2.77/1.40  #Partial instantiations: 0
% 2.77/1.40  #Strategies tried      : 1
% 2.77/1.40  
% 2.77/1.40  Timing (in seconds)
% 2.77/1.40  ----------------------
% 2.77/1.40  Preprocessing        : 0.30
% 2.77/1.40  Parsing              : 0.16
% 2.77/1.40  CNF conversion       : 0.02
% 2.77/1.40  Main loop            : 0.33
% 2.77/1.40  Inferencing          : 0.11
% 2.77/1.40  Reduction            : 0.11
% 2.77/1.40  Demodulation         : 0.09
% 2.77/1.40  BG Simplification    : 0.02
% 2.77/1.40  Subsumption          : 0.07
% 2.77/1.40  Abstraction          : 0.02
% 2.77/1.40  MUC search           : 0.00
% 2.77/1.40  Cooper               : 0.00
% 2.77/1.40  Total                : 0.65
% 2.77/1.40  Index Insertion      : 0.00
% 2.77/1.40  Index Deletion       : 0.00
% 2.77/1.40  Index Matching       : 0.00
% 2.77/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
