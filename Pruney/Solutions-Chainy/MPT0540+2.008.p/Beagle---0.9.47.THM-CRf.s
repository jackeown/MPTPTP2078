%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:32 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 (  85 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_84,plain,(
    ! [A_35,B_36,C_37] :
      ( k8_relat_1(A_35,k5_relat_1(B_36,C_37)) = k5_relat_1(B_36,k8_relat_1(A_35,C_37))
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_96,plain,(
    ! [A_21,A_35,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),k8_relat_1(A_35,B_22)) = k8_relat_1(A_35,k7_relat_1(B_22,A_21))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_84])).

tff(c_102,plain,(
    ! [A_21,A_35,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),k8_relat_1(A_35,B_22)) = k8_relat_1(A_35,k7_relat_1(B_22,A_21))
      | ~ v1_relat_1(B_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_96])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_277,plain,(
    ! [A_53,B_54,C_55] :
      ( k5_relat_1(k5_relat_1(A_53,B_54),C_55) = k5_relat_1(A_53,k5_relat_1(B_54,C_55))
      | ~ v1_relat_1(C_55)
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_332,plain,(
    ! [A_21,B_22,C_55] :
      ( k5_relat_1(k6_relat_1(A_21),k5_relat_1(B_22,C_55)) = k5_relat_1(k7_relat_1(B_22,A_21),C_55)
      | ~ v1_relat_1(C_55)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_277])).

tff(c_602,plain,(
    ! [A_74,B_75,C_76] :
      ( k5_relat_1(k6_relat_1(A_74),k5_relat_1(B_75,C_76)) = k5_relat_1(k7_relat_1(B_75,A_74),C_76)
      | ~ v1_relat_1(C_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_332])).

tff(c_664,plain,(
    ! [B_9,A_74,A_8] :
      ( k5_relat_1(k7_relat_1(B_9,A_74),k6_relat_1(A_8)) = k5_relat_1(k6_relat_1(A_74),k8_relat_1(A_8,B_9))
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_602])).

tff(c_752,plain,(
    ! [B_80,A_81,A_82] :
      ( k5_relat_1(k7_relat_1(B_80,A_81),k6_relat_1(A_82)) = k5_relat_1(k6_relat_1(A_81),k8_relat_1(A_82,B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_664])).

tff(c_65,plain,(
    ! [B_32,C_33,A_34] :
      ( k7_relat_1(k5_relat_1(B_32,C_33),A_34) = k5_relat_1(k7_relat_1(B_32,A_34),C_33)
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    ! [B_9,A_34,A_8] :
      ( k5_relat_1(k7_relat_1(B_9,A_34),k6_relat_1(A_8)) = k7_relat_1(k8_relat_1(A_8,B_9),A_34)
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_81,plain,(
    ! [B_9,A_34,A_8] :
      ( k5_relat_1(k7_relat_1(B_9,A_34),k6_relat_1(A_8)) = k7_relat_1(k8_relat_1(A_8,B_9),A_34)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_74])).

tff(c_987,plain,(
    ! [A_89,A_90,B_91] :
      ( k5_relat_1(k6_relat_1(A_89),k8_relat_1(A_90,B_91)) = k7_relat_1(k8_relat_1(A_90,B_91),A_89)
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_81])).

tff(c_1265,plain,(
    ! [A_101,B_102,A_103] :
      ( k8_relat_1(A_101,k7_relat_1(B_102,A_103)) = k7_relat_1(k8_relat_1(A_101,B_102),A_103)
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_987])).

tff(c_16,plain,(
    k8_relat_1('#skF_1',k7_relat_1('#skF_3','#skF_2')) != k7_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1289,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1265,c_16])).

tff(c_1305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:56:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.46  
% 3.10/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.47  %$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.10/1.47  
% 3.10/1.47  %Foreground sorts:
% 3.10/1.47  
% 3.10/1.47  
% 3.10/1.47  %Background operators:
% 3.10/1.47  
% 3.10/1.47  
% 3.10/1.47  %Foreground operators:
% 3.10/1.47  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.10/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.10/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.10/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.47  
% 3.10/1.48  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 3.10/1.48  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.10/1.48  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.10/1.48  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_relat_1)).
% 3.10/1.48  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 3.10/1.48  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 3.10/1.48  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 3.10/1.48  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.10/1.48  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.48  tff(c_14, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.10/1.48  tff(c_84, plain, (![A_35, B_36, C_37]: (k8_relat_1(A_35, k5_relat_1(B_36, C_37))=k5_relat_1(B_36, k8_relat_1(A_35, C_37)) | ~v1_relat_1(C_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.10/1.48  tff(c_96, plain, (![A_21, A_35, B_22]: (k5_relat_1(k6_relat_1(A_21), k8_relat_1(A_35, B_22))=k8_relat_1(A_35, k7_relat_1(B_22, A_21)) | ~v1_relat_1(B_22) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_14, c_84])).
% 3.10/1.48  tff(c_102, plain, (![A_21, A_35, B_22]: (k5_relat_1(k6_relat_1(A_21), k8_relat_1(A_35, B_22))=k8_relat_1(A_35, k7_relat_1(B_22, A_21)) | ~v1_relat_1(B_22))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_96])).
% 3.10/1.48  tff(c_8, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.10/1.48  tff(c_277, plain, (![A_53, B_54, C_55]: (k5_relat_1(k5_relat_1(A_53, B_54), C_55)=k5_relat_1(A_53, k5_relat_1(B_54, C_55)) | ~v1_relat_1(C_55) | ~v1_relat_1(B_54) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.10/1.48  tff(c_332, plain, (![A_21, B_22, C_55]: (k5_relat_1(k6_relat_1(A_21), k5_relat_1(B_22, C_55))=k5_relat_1(k7_relat_1(B_22, A_21), C_55) | ~v1_relat_1(C_55) | ~v1_relat_1(B_22) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_14, c_277])).
% 3.10/1.48  tff(c_602, plain, (![A_74, B_75, C_76]: (k5_relat_1(k6_relat_1(A_74), k5_relat_1(B_75, C_76))=k5_relat_1(k7_relat_1(B_75, A_74), C_76) | ~v1_relat_1(C_76) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_332])).
% 3.10/1.48  tff(c_664, plain, (![B_9, A_74, A_8]: (k5_relat_1(k7_relat_1(B_9, A_74), k6_relat_1(A_8))=k5_relat_1(k6_relat_1(A_74), k8_relat_1(A_8, B_9)) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(B_9) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_8, c_602])).
% 3.10/1.48  tff(c_752, plain, (![B_80, A_81, A_82]: (k5_relat_1(k7_relat_1(B_80, A_81), k6_relat_1(A_82))=k5_relat_1(k6_relat_1(A_81), k8_relat_1(A_82, B_80)) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_664])).
% 3.10/1.48  tff(c_65, plain, (![B_32, C_33, A_34]: (k7_relat_1(k5_relat_1(B_32, C_33), A_34)=k5_relat_1(k7_relat_1(B_32, A_34), C_33) | ~v1_relat_1(C_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.10/1.48  tff(c_74, plain, (![B_9, A_34, A_8]: (k5_relat_1(k7_relat_1(B_9, A_34), k6_relat_1(A_8))=k7_relat_1(k8_relat_1(A_8, B_9), A_34) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(B_9) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_8, c_65])).
% 3.10/1.48  tff(c_81, plain, (![B_9, A_34, A_8]: (k5_relat_1(k7_relat_1(B_9, A_34), k6_relat_1(A_8))=k7_relat_1(k8_relat_1(A_8, B_9), A_34) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_74])).
% 3.10/1.48  tff(c_987, plain, (![A_89, A_90, B_91]: (k5_relat_1(k6_relat_1(A_89), k8_relat_1(A_90, B_91))=k7_relat_1(k8_relat_1(A_90, B_91), A_89) | ~v1_relat_1(B_91) | ~v1_relat_1(B_91))), inference(superposition, [status(thm), theory('equality')], [c_752, c_81])).
% 3.10/1.48  tff(c_1265, plain, (![A_101, B_102, A_103]: (k8_relat_1(A_101, k7_relat_1(B_102, A_103))=k7_relat_1(k8_relat_1(A_101, B_102), A_103) | ~v1_relat_1(B_102) | ~v1_relat_1(B_102) | ~v1_relat_1(B_102))), inference(superposition, [status(thm), theory('equality')], [c_102, c_987])).
% 3.10/1.48  tff(c_16, plain, (k8_relat_1('#skF_1', k7_relat_1('#skF_3', '#skF_2'))!=k7_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.10/1.48  tff(c_1289, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1265, c_16])).
% 3.10/1.48  tff(c_1305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1289])).
% 3.10/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.48  
% 3.10/1.48  Inference rules
% 3.10/1.48  ----------------------
% 3.10/1.48  #Ref     : 1
% 3.10/1.48  #Sup     : 284
% 3.10/1.48  #Fact    : 0
% 3.10/1.48  #Define  : 0
% 3.10/1.48  #Split   : 0
% 3.10/1.48  #Chain   : 0
% 3.10/1.48  #Close   : 0
% 3.10/1.48  
% 3.10/1.48  Ordering : KBO
% 3.10/1.48  
% 3.10/1.48  Simplification rules
% 3.10/1.48  ----------------------
% 3.10/1.48  #Subsume      : 27
% 3.10/1.48  #Demod        : 226
% 3.10/1.48  #Tautology    : 97
% 3.10/1.48  #SimpNegUnit  : 0
% 3.10/1.48  #BackRed      : 2
% 3.10/1.48  
% 3.10/1.48  #Partial instantiations: 0
% 3.10/1.48  #Strategies tried      : 1
% 3.10/1.48  
% 3.10/1.48  Timing (in seconds)
% 3.10/1.48  ----------------------
% 3.10/1.48  Preprocessing        : 0.28
% 3.10/1.48  Parsing              : 0.15
% 3.10/1.48  CNF conversion       : 0.02
% 3.10/1.48  Main loop            : 0.43
% 3.10/1.48  Inferencing          : 0.17
% 3.10/1.48  Reduction            : 0.13
% 3.10/1.48  Demodulation         : 0.10
% 3.10/1.48  BG Simplification    : 0.03
% 3.10/1.48  Subsumption          : 0.07
% 3.10/1.48  Abstraction          : 0.03
% 3.10/1.48  MUC search           : 0.00
% 3.10/1.48  Cooper               : 0.00
% 3.10/1.48  Total                : 0.73
% 3.10/1.48  Index Insertion      : 0.00
% 3.10/1.48  Index Deletion       : 0.00
% 3.10/1.48  Index Matching       : 0.00
% 3.10/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
