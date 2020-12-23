%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:31 EST 2020

% Result     : Theorem 5.22s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 (  70 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k7_relat_1(A_2,B_3))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = k8_relat_1(A_6,B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_15,B_16] :
      ( k5_relat_1(k6_relat_1(A_15),B_16) = k7_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ! [A_30,B_31,C_32] :
      ( k5_relat_1(k5_relat_1(A_30,B_31),C_32) = k5_relat_1(A_30,k5_relat_1(B_31,C_32))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    ! [A_15,B_16,C_32] :
      ( k5_relat_1(k6_relat_1(A_15),k5_relat_1(B_16,C_32)) = k5_relat_1(k7_relat_1(B_16,A_15),C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_66])).

tff(c_103,plain,(
    ! [A_33,B_34,C_35] :
      ( k5_relat_1(k6_relat_1(A_33),k5_relat_1(B_34,C_35)) = k5_relat_1(k7_relat_1(B_34,A_33),C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_85])).

tff(c_134,plain,(
    ! [B_7,A_33,A_6] :
      ( k5_relat_1(k7_relat_1(B_7,A_33),k6_relat_1(A_6)) = k5_relat_1(k6_relat_1(A_33),k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(k6_relat_1(A_6))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_103])).

tff(c_482,plain,(
    ! [B_63,A_64,A_65] :
      ( k5_relat_1(k7_relat_1(B_63,A_64),k6_relat_1(A_65)) = k5_relat_1(k6_relat_1(A_64),k8_relat_1(A_65,B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_134])).

tff(c_738,plain,(
    ! [A_72,A_73,B_74] :
      ( k5_relat_1(k6_relat_1(A_72),k8_relat_1(A_73,B_74)) = k8_relat_1(A_73,k7_relat_1(B_74,A_72))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(k7_relat_1(B_74,A_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_482])).

tff(c_3633,plain,(
    ! [A_206,B_207,A_208] :
      ( k8_relat_1(A_206,k7_relat_1(B_207,A_208)) = k7_relat_1(k8_relat_1(A_206,B_207),A_208)
      | ~ v1_relat_1(k8_relat_1(A_206,B_207))
      | ~ v1_relat_1(B_207)
      | ~ v1_relat_1(k7_relat_1(B_207,A_208)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_12])).

tff(c_3661,plain,(
    ! [A_209,B_210,A_211] :
      ( k8_relat_1(A_209,k7_relat_1(B_210,A_211)) = k7_relat_1(k8_relat_1(A_209,B_210),A_211)
      | ~ v1_relat_1(k7_relat_1(B_210,A_211))
      | ~ v1_relat_1(B_210) ) ),
    inference(resolution,[status(thm)],[c_6,c_3633])).

tff(c_3693,plain,(
    ! [A_212,A_213,B_214] :
      ( k8_relat_1(A_212,k7_relat_1(A_213,B_214)) = k7_relat_1(k8_relat_1(A_212,A_213),B_214)
      | ~ v1_relat_1(A_213) ) ),
    inference(resolution,[status(thm)],[c_4,c_3661])).

tff(c_14,plain,(
    k8_relat_1('#skF_1',k7_relat_1('#skF_3','#skF_2')) != k7_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3722,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3693,c_14])).

tff(c_3752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n010.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 18:29:14 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.22/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/2.07  
% 5.22/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/2.07  %$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.22/2.07  
% 5.22/2.07  %Foreground sorts:
% 5.22/2.07  
% 5.22/2.07  
% 5.22/2.07  %Background operators:
% 5.22/2.07  
% 5.22/2.07  
% 5.22/2.07  %Foreground operators:
% 5.22/2.07  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.22/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.22/2.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.22/2.07  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.22/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.22/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.22/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.22/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.22/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.22/2.07  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.22/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.22/2.07  
% 5.35/2.08  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 5.35/2.08  tff(f_31, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.35/2.08  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 5.35/2.08  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 5.35/2.08  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 5.35/2.08  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 5.35/2.08  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 5.35/2.08  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.35/2.08  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k7_relat_1(A_2, B_3)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.35/2.08  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k8_relat_1(A_4, B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.35/2.08  tff(c_8, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=k8_relat_1(A_6, B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.35/2.08  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.35/2.08  tff(c_12, plain, (![A_15, B_16]: (k5_relat_1(k6_relat_1(A_15), B_16)=k7_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.35/2.08  tff(c_66, plain, (![A_30, B_31, C_32]: (k5_relat_1(k5_relat_1(A_30, B_31), C_32)=k5_relat_1(A_30, k5_relat_1(B_31, C_32)) | ~v1_relat_1(C_32) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.35/2.08  tff(c_85, plain, (![A_15, B_16, C_32]: (k5_relat_1(k6_relat_1(A_15), k5_relat_1(B_16, C_32))=k5_relat_1(k7_relat_1(B_16, A_15), C_32) | ~v1_relat_1(C_32) | ~v1_relat_1(B_16) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(B_16))), inference(superposition, [status(thm), theory('equality')], [c_12, c_66])).
% 5.35/2.08  tff(c_103, plain, (![A_33, B_34, C_35]: (k5_relat_1(k6_relat_1(A_33), k5_relat_1(B_34, C_35))=k5_relat_1(k7_relat_1(B_34, A_33), C_35) | ~v1_relat_1(C_35) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_85])).
% 5.35/2.08  tff(c_134, plain, (![B_7, A_33, A_6]: (k5_relat_1(k7_relat_1(B_7, A_33), k6_relat_1(A_6))=k5_relat_1(k6_relat_1(A_33), k8_relat_1(A_6, B_7)) | ~v1_relat_1(k6_relat_1(A_6)) | ~v1_relat_1(B_7) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_103])).
% 5.35/2.08  tff(c_482, plain, (![B_63, A_64, A_65]: (k5_relat_1(k7_relat_1(B_63, A_64), k6_relat_1(A_65))=k5_relat_1(k6_relat_1(A_64), k8_relat_1(A_65, B_63)) | ~v1_relat_1(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_134])).
% 5.35/2.08  tff(c_738, plain, (![A_72, A_73, B_74]: (k5_relat_1(k6_relat_1(A_72), k8_relat_1(A_73, B_74))=k8_relat_1(A_73, k7_relat_1(B_74, A_72)) | ~v1_relat_1(B_74) | ~v1_relat_1(k7_relat_1(B_74, A_72)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_482])).
% 5.35/2.08  tff(c_3633, plain, (![A_206, B_207, A_208]: (k8_relat_1(A_206, k7_relat_1(B_207, A_208))=k7_relat_1(k8_relat_1(A_206, B_207), A_208) | ~v1_relat_1(k8_relat_1(A_206, B_207)) | ~v1_relat_1(B_207) | ~v1_relat_1(k7_relat_1(B_207, A_208)))), inference(superposition, [status(thm), theory('equality')], [c_738, c_12])).
% 5.35/2.08  tff(c_3661, plain, (![A_209, B_210, A_211]: (k8_relat_1(A_209, k7_relat_1(B_210, A_211))=k7_relat_1(k8_relat_1(A_209, B_210), A_211) | ~v1_relat_1(k7_relat_1(B_210, A_211)) | ~v1_relat_1(B_210))), inference(resolution, [status(thm)], [c_6, c_3633])).
% 5.35/2.08  tff(c_3693, plain, (![A_212, A_213, B_214]: (k8_relat_1(A_212, k7_relat_1(A_213, B_214))=k7_relat_1(k8_relat_1(A_212, A_213), B_214) | ~v1_relat_1(A_213))), inference(resolution, [status(thm)], [c_4, c_3661])).
% 5.35/2.08  tff(c_14, plain, (k8_relat_1('#skF_1', k7_relat_1('#skF_3', '#skF_2'))!=k7_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.35/2.08  tff(c_3722, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3693, c_14])).
% 5.35/2.08  tff(c_3752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_3722])).
% 5.35/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.08  
% 5.35/2.08  Inference rules
% 5.35/2.08  ----------------------
% 5.35/2.08  #Ref     : 0
% 5.35/2.08  #Sup     : 807
% 5.35/2.08  #Fact    : 0
% 5.35/2.08  #Define  : 0
% 5.35/2.08  #Split   : 0
% 5.35/2.08  #Chain   : 0
% 5.35/2.08  #Close   : 0
% 5.35/2.08  
% 5.35/2.08  Ordering : KBO
% 5.35/2.08  
% 5.35/2.08  Simplification rules
% 5.35/2.08  ----------------------
% 5.35/2.08  #Subsume      : 50
% 5.35/2.08  #Demod        : 1476
% 5.35/2.08  #Tautology    : 263
% 5.35/2.08  #SimpNegUnit  : 0
% 5.35/2.08  #BackRed      : 2
% 5.35/2.08  
% 5.35/2.08  #Partial instantiations: 0
% 5.35/2.08  #Strategies tried      : 1
% 5.35/2.08  
% 5.35/2.08  Timing (in seconds)
% 5.35/2.08  ----------------------
% 5.35/2.09  Preprocessing        : 0.32
% 5.35/2.09  Parsing              : 0.17
% 5.35/2.09  CNF conversion       : 0.02
% 5.35/2.09  Main loop            : 0.94
% 5.35/2.09  Inferencing          : 0.36
% 5.35/2.09  Reduction            : 0.33
% 5.35/2.09  Demodulation         : 0.25
% 5.35/2.09  BG Simplification    : 0.06
% 5.35/2.09  Subsumption          : 0.14
% 5.35/2.09  Abstraction          : 0.09
% 5.35/2.09  MUC search           : 0.00
% 5.35/2.09  Cooper               : 0.00
% 5.35/2.09  Total                : 1.29
% 5.35/2.09  Index Insertion      : 0.00
% 5.35/2.09  Index Deletion       : 0.00
% 5.35/2.09  Index Matching       : 0.00
% 5.35/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
