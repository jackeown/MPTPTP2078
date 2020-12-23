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
% DateTime   : Thu Dec  3 10:00:31 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 (  85 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_34,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( k5_relat_1(k6_relat_1(A_24),B_25) = k7_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_134,plain,(
    ! [A_50,B_51,C_52] :
      ( k8_relat_1(A_50,k5_relat_1(B_51,C_52)) = k5_relat_1(B_51,k8_relat_1(A_50,C_52))
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_149,plain,(
    ! [A_24,A_50,B_25] :
      ( k5_relat_1(k6_relat_1(A_24),k8_relat_1(A_50,B_25)) = k8_relat_1(A_50,k7_relat_1(B_25,A_24))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(k6_relat_1(A_24))
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_134])).

tff(c_157,plain,(
    ! [A_24,A_50,B_25] :
      ( k5_relat_1(k6_relat_1(A_24),k8_relat_1(A_50,B_25)) = k8_relat_1(A_50,k7_relat_1(B_25,A_24))
      | ~ v1_relat_1(B_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_149])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k5_relat_1(B_12,k6_relat_1(A_11)) = k8_relat_1(A_11,B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_266,plain,(
    ! [A_62,B_63,C_64] :
      ( k5_relat_1(k5_relat_1(A_62,B_63),C_64) = k5_relat_1(A_62,k5_relat_1(B_63,C_64))
      | ~ v1_relat_1(C_64)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_318,plain,(
    ! [A_24,B_25,C_64] :
      ( k5_relat_1(k6_relat_1(A_24),k5_relat_1(B_25,C_64)) = k5_relat_1(k7_relat_1(B_25,A_24),C_64)
      | ~ v1_relat_1(C_64)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(k6_relat_1(A_24))
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_266])).

tff(c_571,plain,(
    ! [A_79,B_80,C_81] :
      ( k5_relat_1(k6_relat_1(A_79),k5_relat_1(B_80,C_81)) = k5_relat_1(k7_relat_1(B_80,A_79),C_81)
      | ~ v1_relat_1(C_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_318])).

tff(c_636,plain,(
    ! [B_12,A_79,A_11] :
      ( k5_relat_1(k7_relat_1(B_12,A_79),k6_relat_1(A_11)) = k5_relat_1(k6_relat_1(A_79),k8_relat_1(A_11,B_12))
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_571])).

tff(c_809,plain,(
    ! [B_93,A_94,A_95] :
      ( k5_relat_1(k7_relat_1(B_93,A_94),k6_relat_1(A_95)) = k5_relat_1(k6_relat_1(A_94),k8_relat_1(A_95,B_93))
      | ~ v1_relat_1(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_636])).

tff(c_91,plain,(
    ! [B_44,C_45,A_46] :
      ( k7_relat_1(k5_relat_1(B_44,C_45),A_46) = k5_relat_1(k7_relat_1(B_44,A_46),C_45)
      | ~ v1_relat_1(C_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_100,plain,(
    ! [B_12,A_46,A_11] :
      ( k5_relat_1(k7_relat_1(B_12,A_46),k6_relat_1(A_11)) = k7_relat_1(k8_relat_1(A_11,B_12),A_46)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_91])).

tff(c_107,plain,(
    ! [B_12,A_46,A_11] :
      ( k5_relat_1(k7_relat_1(B_12,A_46),k6_relat_1(A_11)) = k7_relat_1(k8_relat_1(A_11,B_12),A_46)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_100])).

tff(c_1097,plain,(
    ! [A_102,A_103,B_104] :
      ( k5_relat_1(k6_relat_1(A_102),k8_relat_1(A_103,B_104)) = k7_relat_1(k8_relat_1(A_103,B_104),A_102)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_107])).

tff(c_1325,plain,(
    ! [A_117,B_118,A_119] :
      ( k8_relat_1(A_117,k7_relat_1(B_118,A_119)) = k7_relat_1(k8_relat_1(A_117,B_118),A_119)
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_1097])).

tff(c_26,plain,(
    k8_relat_1('#skF_3',k7_relat_1('#skF_5','#skF_4')) != k7_relat_1(k8_relat_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1349,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1325,c_26])).

tff(c_1365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:45:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.45  
% 2.75/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.46  %$ r2_hidden > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.75/1.46  
% 2.75/1.46  %Foreground sorts:
% 2.75/1.46  
% 2.75/1.46  
% 2.75/1.46  %Background operators:
% 2.75/1.46  
% 2.75/1.46  
% 2.75/1.46  %Foreground operators:
% 2.75/1.46  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.75/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.75/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.75/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.75/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.46  
% 3.15/1.47  tff(f_71, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 3.15/1.47  tff(f_34, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.15/1.47  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.15/1.47  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 3.15/1.47  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 3.15/1.47  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 3.15/1.47  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 3.15/1.47  tff(c_28, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.15/1.47  tff(c_14, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.15/1.47  tff(c_24, plain, (![A_24, B_25]: (k5_relat_1(k6_relat_1(A_24), B_25)=k7_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.15/1.47  tff(c_134, plain, (![A_50, B_51, C_52]: (k8_relat_1(A_50, k5_relat_1(B_51, C_52))=k5_relat_1(B_51, k8_relat_1(A_50, C_52)) | ~v1_relat_1(C_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.15/1.47  tff(c_149, plain, (![A_24, A_50, B_25]: (k5_relat_1(k6_relat_1(A_24), k8_relat_1(A_50, B_25))=k8_relat_1(A_50, k7_relat_1(B_25, A_24)) | ~v1_relat_1(B_25) | ~v1_relat_1(k6_relat_1(A_24)) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_24, c_134])).
% 3.15/1.47  tff(c_157, plain, (![A_24, A_50, B_25]: (k5_relat_1(k6_relat_1(A_24), k8_relat_1(A_50, B_25))=k8_relat_1(A_50, k7_relat_1(B_25, A_24)) | ~v1_relat_1(B_25))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_149])).
% 3.15/1.47  tff(c_18, plain, (![B_12, A_11]: (k5_relat_1(B_12, k6_relat_1(A_11))=k8_relat_1(A_11, B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.15/1.47  tff(c_266, plain, (![A_62, B_63, C_64]: (k5_relat_1(k5_relat_1(A_62, B_63), C_64)=k5_relat_1(A_62, k5_relat_1(B_63, C_64)) | ~v1_relat_1(C_64) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.47  tff(c_318, plain, (![A_24, B_25, C_64]: (k5_relat_1(k6_relat_1(A_24), k5_relat_1(B_25, C_64))=k5_relat_1(k7_relat_1(B_25, A_24), C_64) | ~v1_relat_1(C_64) | ~v1_relat_1(B_25) | ~v1_relat_1(k6_relat_1(A_24)) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_24, c_266])).
% 3.15/1.47  tff(c_571, plain, (![A_79, B_80, C_81]: (k5_relat_1(k6_relat_1(A_79), k5_relat_1(B_80, C_81))=k5_relat_1(k7_relat_1(B_80, A_79), C_81) | ~v1_relat_1(C_81) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_318])).
% 3.15/1.47  tff(c_636, plain, (![B_12, A_79, A_11]: (k5_relat_1(k7_relat_1(B_12, A_79), k6_relat_1(A_11))=k5_relat_1(k6_relat_1(A_79), k8_relat_1(A_11, B_12)) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(B_12) | ~v1_relat_1(B_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_571])).
% 3.15/1.47  tff(c_809, plain, (![B_93, A_94, A_95]: (k5_relat_1(k7_relat_1(B_93, A_94), k6_relat_1(A_95))=k5_relat_1(k6_relat_1(A_94), k8_relat_1(A_95, B_93)) | ~v1_relat_1(B_93))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_636])).
% 3.15/1.47  tff(c_91, plain, (![B_44, C_45, A_46]: (k7_relat_1(k5_relat_1(B_44, C_45), A_46)=k5_relat_1(k7_relat_1(B_44, A_46), C_45) | ~v1_relat_1(C_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.47  tff(c_100, plain, (![B_12, A_46, A_11]: (k5_relat_1(k7_relat_1(B_12, A_46), k6_relat_1(A_11))=k7_relat_1(k8_relat_1(A_11, B_12), A_46) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(B_12) | ~v1_relat_1(B_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_91])).
% 3.15/1.47  tff(c_107, plain, (![B_12, A_46, A_11]: (k5_relat_1(k7_relat_1(B_12, A_46), k6_relat_1(A_11))=k7_relat_1(k8_relat_1(A_11, B_12), A_46) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_100])).
% 3.15/1.47  tff(c_1097, plain, (![A_102, A_103, B_104]: (k5_relat_1(k6_relat_1(A_102), k8_relat_1(A_103, B_104))=k7_relat_1(k8_relat_1(A_103, B_104), A_102) | ~v1_relat_1(B_104) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_809, c_107])).
% 3.15/1.47  tff(c_1325, plain, (![A_117, B_118, A_119]: (k8_relat_1(A_117, k7_relat_1(B_118, A_119))=k7_relat_1(k8_relat_1(A_117, B_118), A_119) | ~v1_relat_1(B_118) | ~v1_relat_1(B_118) | ~v1_relat_1(B_118))), inference(superposition, [status(thm), theory('equality')], [c_157, c_1097])).
% 3.15/1.47  tff(c_26, plain, (k8_relat_1('#skF_3', k7_relat_1('#skF_5', '#skF_4'))!=k7_relat_1(k8_relat_1('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.15/1.47  tff(c_1349, plain, (~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1325, c_26])).
% 3.15/1.47  tff(c_1365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1349])).
% 3.15/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  Inference rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Ref     : 0
% 3.15/1.47  #Sup     : 294
% 3.15/1.47  #Fact    : 0
% 3.15/1.47  #Define  : 0
% 3.15/1.47  #Split   : 0
% 3.15/1.47  #Chain   : 0
% 3.15/1.47  #Close   : 0
% 3.15/1.47  
% 3.15/1.47  Ordering : KBO
% 3.15/1.47  
% 3.15/1.47  Simplification rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Subsume      : 28
% 3.15/1.47  #Demod        : 230
% 3.15/1.47  #Tautology    : 102
% 3.15/1.47  #SimpNegUnit  : 0
% 3.15/1.47  #BackRed      : 2
% 3.15/1.47  
% 3.15/1.47  #Partial instantiations: 0
% 3.15/1.47  #Strategies tried      : 1
% 3.15/1.47  
% 3.15/1.47  Timing (in seconds)
% 3.15/1.47  ----------------------
% 3.15/1.47  Preprocessing        : 0.29
% 3.15/1.47  Parsing              : 0.15
% 3.15/1.47  CNF conversion       : 0.02
% 3.15/1.47  Main loop            : 0.42
% 3.15/1.47  Inferencing          : 0.17
% 3.15/1.47  Reduction            : 0.13
% 3.15/1.47  Demodulation         : 0.09
% 3.15/1.47  BG Simplification    : 0.03
% 3.15/1.47  Subsumption          : 0.07
% 3.15/1.47  Abstraction          : 0.04
% 3.15/1.47  MUC search           : 0.00
% 3.15/1.47  Cooper               : 0.00
% 3.15/1.47  Total                : 0.74
% 3.15/1.47  Index Insertion      : 0.00
% 3.15/1.47  Index Deletion       : 0.00
% 3.15/1.47  Index Matching       : 0.00
% 3.15/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
