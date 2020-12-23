%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:31 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   52 (  79 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 132 expanded)
%              Number of equality atoms :   28 (  47 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_22,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_99,plain,(
    ! [B_32,C_33,A_34] :
      ( k10_relat_1(k5_relat_1(B_32,C_33),A_34) = k10_relat_1(B_32,k10_relat_1(C_33,A_34))
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_112,plain,(
    ! [A_11,B_12,A_34] :
      ( k10_relat_1(k6_relat_1(A_11),k10_relat_1(B_12,A_34)) = k10_relat_1(k7_relat_1(B_12,A_11),A_34)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_99])).

tff(c_120,plain,(
    ! [A_11,B_12,A_34] :
      ( k10_relat_1(k6_relat_1(A_11),k10_relat_1(B_12,A_34)) = k10_relat_1(k7_relat_1(B_12,A_11),A_34)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_112])).

tff(c_12,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_49,plain,(
    ! [A_20] :
      ( k10_relat_1(A_20,k2_relat_1(A_20)) = k1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [A_10] :
      ( k10_relat_1(k6_relat_1(A_10),A_10) = k1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_49])).

tff(c_62,plain,(
    ! [A_10] : k10_relat_1(k6_relat_1(A_10),A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12,c_58])).

tff(c_89,plain,(
    ! [B_30,A_31] :
      ( v4_relat_1(B_30,A_31)
      | ~ r1_tarski(k1_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_10,A_31] :
      ( v4_relat_1(k6_relat_1(A_10),A_31)
      | ~ r1_tarski(A_10,A_31)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_121,plain,(
    ! [A_35,A_36] :
      ( v4_relat_1(k6_relat_1(A_35),A_36)
      | ~ r1_tarski(A_35,A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_95])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_127,plain,(
    ! [A_35,A_36] :
      ( k7_relat_1(k6_relat_1(A_35),A_36) = k6_relat_1(A_35)
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ r1_tarski(A_35,A_36) ) ),
    inference(resolution,[status(thm)],[c_121,c_10])).

tff(c_131,plain,(
    ! [A_35,A_36] :
      ( k7_relat_1(k6_relat_1(A_35),A_36) = k6_relat_1(A_35)
      | ~ r1_tarski(A_35,A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_127])).

tff(c_6,plain,(
    ! [A_3] :
      ( k10_relat_1(A_3,k2_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_141,plain,(
    ! [A_39,B_40,A_41] :
      ( k10_relat_1(k6_relat_1(A_39),k10_relat_1(B_40,A_41)) = k10_relat_1(k7_relat_1(B_40,A_39),A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_112])).

tff(c_179,plain,(
    ! [A_42,A_43] :
      ( k10_relat_1(k7_relat_1(A_42,A_43),k2_relat_1(A_42)) = k10_relat_1(k6_relat_1(A_43),k1_relat_1(A_42))
      | ~ v1_relat_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_141])).

tff(c_191,plain,(
    ! [A_36,A_35] :
      ( k10_relat_1(k6_relat_1(A_36),k1_relat_1(k6_relat_1(A_35))) = k10_relat_1(k6_relat_1(A_35),k2_relat_1(k6_relat_1(A_35)))
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ r1_tarski(A_35,A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_179])).

tff(c_201,plain,(
    ! [A_44,A_45] :
      ( k10_relat_1(k6_relat_1(A_44),A_45) = A_45
      | ~ r1_tarski(A_45,A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_62,c_12,c_14,c_191])).

tff(c_640,plain,(
    ! [B_63,A_64,A_65] :
      ( k10_relat_1(k7_relat_1(B_63,A_64),A_65) = k10_relat_1(B_63,A_65)
      | ~ r1_tarski(k10_relat_1(B_63,A_65),A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_201])).

tff(c_682,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_640])).

tff(c_694,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_682])).

tff(c_696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_694])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.34  
% 2.46/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.34  %$ v4_relat_1 > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.46/1.34  
% 2.46/1.34  %Foreground sorts:
% 2.46/1.34  
% 2.46/1.34  
% 2.46/1.34  %Background operators:
% 2.46/1.34  
% 2.46/1.34  
% 2.46/1.34  %Foreground operators:
% 2.46/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.46/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.46/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.46/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.46/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.46/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.46/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.34  
% 2.46/1.36  tff(f_70, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 2.46/1.36  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.46/1.36  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.46/1.36  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 2.46/1.36  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.46/1.36  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.46/1.36  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.46/1.36  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.46/1.36  tff(c_22, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.46/1.36  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.46/1.36  tff(c_24, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.46/1.36  tff(c_18, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.36  tff(c_16, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.36  tff(c_99, plain, (![B_32, C_33, A_34]: (k10_relat_1(k5_relat_1(B_32, C_33), A_34)=k10_relat_1(B_32, k10_relat_1(C_33, A_34)) | ~v1_relat_1(C_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.46/1.36  tff(c_112, plain, (![A_11, B_12, A_34]: (k10_relat_1(k6_relat_1(A_11), k10_relat_1(B_12, A_34))=k10_relat_1(k7_relat_1(B_12, A_11), A_34) | ~v1_relat_1(B_12) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(B_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_99])).
% 2.46/1.36  tff(c_120, plain, (![A_11, B_12, A_34]: (k10_relat_1(k6_relat_1(A_11), k10_relat_1(B_12, A_34))=k10_relat_1(k7_relat_1(B_12, A_11), A_34) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_112])).
% 2.46/1.36  tff(c_12, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.46/1.36  tff(c_14, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.46/1.36  tff(c_49, plain, (![A_20]: (k10_relat_1(A_20, k2_relat_1(A_20))=k1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.46/1.36  tff(c_58, plain, (![A_10]: (k10_relat_1(k6_relat_1(A_10), A_10)=k1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_49])).
% 2.46/1.36  tff(c_62, plain, (![A_10]: (k10_relat_1(k6_relat_1(A_10), A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12, c_58])).
% 2.46/1.36  tff(c_89, plain, (![B_30, A_31]: (v4_relat_1(B_30, A_31) | ~r1_tarski(k1_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.36  tff(c_95, plain, (![A_10, A_31]: (v4_relat_1(k6_relat_1(A_10), A_31) | ~r1_tarski(A_10, A_31) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 2.46/1.36  tff(c_121, plain, (![A_35, A_36]: (v4_relat_1(k6_relat_1(A_35), A_36) | ~r1_tarski(A_35, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_95])).
% 2.46/1.36  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.36  tff(c_127, plain, (![A_35, A_36]: (k7_relat_1(k6_relat_1(A_35), A_36)=k6_relat_1(A_35) | ~v1_relat_1(k6_relat_1(A_35)) | ~r1_tarski(A_35, A_36))), inference(resolution, [status(thm)], [c_121, c_10])).
% 2.46/1.36  tff(c_131, plain, (![A_35, A_36]: (k7_relat_1(k6_relat_1(A_35), A_36)=k6_relat_1(A_35) | ~r1_tarski(A_35, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_127])).
% 2.46/1.36  tff(c_6, plain, (![A_3]: (k10_relat_1(A_3, k2_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.46/1.36  tff(c_141, plain, (![A_39, B_40, A_41]: (k10_relat_1(k6_relat_1(A_39), k10_relat_1(B_40, A_41))=k10_relat_1(k7_relat_1(B_40, A_39), A_41) | ~v1_relat_1(B_40))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_112])).
% 2.46/1.36  tff(c_179, plain, (![A_42, A_43]: (k10_relat_1(k7_relat_1(A_42, A_43), k2_relat_1(A_42))=k10_relat_1(k6_relat_1(A_43), k1_relat_1(A_42)) | ~v1_relat_1(A_42) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_6, c_141])).
% 2.46/1.36  tff(c_191, plain, (![A_36, A_35]: (k10_relat_1(k6_relat_1(A_36), k1_relat_1(k6_relat_1(A_35)))=k10_relat_1(k6_relat_1(A_35), k2_relat_1(k6_relat_1(A_35))) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(A_35)) | ~r1_tarski(A_35, A_36))), inference(superposition, [status(thm), theory('equality')], [c_131, c_179])).
% 2.46/1.36  tff(c_201, plain, (![A_44, A_45]: (k10_relat_1(k6_relat_1(A_44), A_45)=A_45 | ~r1_tarski(A_45, A_44))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_62, c_12, c_14, c_191])).
% 2.46/1.36  tff(c_640, plain, (![B_63, A_64, A_65]: (k10_relat_1(k7_relat_1(B_63, A_64), A_65)=k10_relat_1(B_63, A_65) | ~r1_tarski(k10_relat_1(B_63, A_65), A_64) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_120, c_201])).
% 2.46/1.36  tff(c_682, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_640])).
% 2.46/1.36  tff(c_694, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_682])).
% 2.46/1.36  tff(c_696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_694])).
% 2.46/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.36  
% 2.46/1.36  Inference rules
% 2.46/1.36  ----------------------
% 2.46/1.36  #Ref     : 0
% 2.46/1.36  #Sup     : 149
% 2.46/1.36  #Fact    : 0
% 2.46/1.36  #Define  : 0
% 2.46/1.36  #Split   : 0
% 2.46/1.36  #Chain   : 0
% 2.46/1.36  #Close   : 0
% 2.46/1.36  
% 2.46/1.36  Ordering : KBO
% 2.46/1.36  
% 2.46/1.36  Simplification rules
% 2.46/1.36  ----------------------
% 2.46/1.36  #Subsume      : 11
% 2.46/1.36  #Demod        : 128
% 2.46/1.36  #Tautology    : 63
% 2.46/1.36  #SimpNegUnit  : 1
% 2.46/1.36  #BackRed      : 0
% 2.46/1.36  
% 2.46/1.36  #Partial instantiations: 0
% 2.46/1.36  #Strategies tried      : 1
% 2.46/1.36  
% 2.46/1.36  Timing (in seconds)
% 2.46/1.36  ----------------------
% 2.46/1.36  Preprocessing        : 0.28
% 2.46/1.36  Parsing              : 0.16
% 2.46/1.36  CNF conversion       : 0.02
% 2.46/1.36  Main loop            : 0.33
% 2.46/1.36  Inferencing          : 0.14
% 2.46/1.36  Reduction            : 0.10
% 2.74/1.36  Demodulation         : 0.08
% 2.74/1.36  BG Simplification    : 0.02
% 2.74/1.36  Subsumption          : 0.05
% 2.74/1.36  Abstraction          : 0.02
% 2.74/1.36  MUC search           : 0.00
% 2.74/1.36  Cooper               : 0.00
% 2.74/1.36  Total                : 0.63
% 2.74/1.36  Index Insertion      : 0.00
% 2.74/1.36  Index Deletion       : 0.00
% 2.74/1.36  Index Matching       : 0.00
% 2.74/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
