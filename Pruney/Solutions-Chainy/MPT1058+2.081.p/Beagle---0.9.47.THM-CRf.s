%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:32 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   47 (  75 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 119 expanded)
%              Number of equality atoms :   28 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_18,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_45,plain,(
    ! [A_18] :
      ( k10_relat_1(A_18,k2_relat_1(A_18)) = k1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [A_6] :
      ( k10_relat_1(k6_relat_1(A_6),A_6) = k1_relat_1(k6_relat_1(A_6))
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_45])).

tff(c_58,plain,(
    ! [A_6] : k10_relat_1(k6_relat_1(A_6),A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6,c_54])).

tff(c_77,plain,(
    ! [B_22,A_23] :
      ( k7_relat_1(B_22,A_23) = B_22
      | ~ r1_tarski(k1_relat_1(B_22),A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    ! [A_6,A_23] :
      ( k7_relat_1(k6_relat_1(A_6),A_23) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_23)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_82,plain,(
    ! [A_6,A_23] :
      ( k7_relat_1(k6_relat_1(A_6),A_23) = k6_relat_1(A_6)
      | ~ r1_tarski(A_6,A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k5_relat_1(k6_relat_1(A_7),B_8) = k7_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    ! [B_26,C_27,A_28] :
      ( k10_relat_1(k5_relat_1(B_26,C_27),A_28) = k10_relat_1(B_26,k10_relat_1(C_27,A_28))
      | ~ v1_relat_1(C_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_105,plain,(
    ! [A_7,B_8,A_28] :
      ( k10_relat_1(k6_relat_1(A_7),k10_relat_1(B_8,A_28)) = k10_relat_1(k7_relat_1(B_8,A_7),A_28)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(B_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_114,plain,(
    ! [A_29,B_30,A_31] :
      ( k10_relat_1(k6_relat_1(A_29),k10_relat_1(B_30,A_31)) = k10_relat_1(k7_relat_1(B_30,A_29),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_136,plain,(
    ! [A_6,A_29] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_6),A_29),A_6) = k10_relat_1(k6_relat_1(A_29),A_6)
      | ~ v1_relat_1(k6_relat_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_114])).

tff(c_193,plain,(
    ! [A_34,A_35] : k10_relat_1(k7_relat_1(k6_relat_1(A_34),A_35),A_34) = k10_relat_1(k6_relat_1(A_35),A_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_136])).

tff(c_205,plain,(
    ! [A_6,A_23] :
      ( k10_relat_1(k6_relat_1(A_6),A_6) = k10_relat_1(k6_relat_1(A_23),A_6)
      | ~ r1_tarski(A_6,A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_193])).

tff(c_209,plain,(
    ! [A_36,A_37] :
      ( k10_relat_1(k6_relat_1(A_36),A_37) = A_37
      | ~ r1_tarski(A_37,A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_205])).

tff(c_113,plain,(
    ! [A_7,B_8,A_28] :
      ( k10_relat_1(k6_relat_1(A_7),k10_relat_1(B_8,A_28)) = k10_relat_1(k7_relat_1(B_8,A_7),A_28)
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_609,plain,(
    ! [B_53,A_54,A_55] :
      ( k10_relat_1(k7_relat_1(B_53,A_54),A_55) = k10_relat_1(B_53,A_55)
      | ~ v1_relat_1(B_53)
      | ~ r1_tarski(k10_relat_1(B_53,A_55),A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_113])).

tff(c_651,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_609])).

tff(c_663,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_651])).

tff(c_665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:31:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.32  
% 2.50/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.33  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.33  
% 2.50/1.33  %Foreground sorts:
% 2.50/1.33  
% 2.50/1.33  
% 2.50/1.33  %Background operators:
% 2.50/1.33  
% 2.50/1.33  
% 2.50/1.33  %Foreground operators:
% 2.50/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.50/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.50/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.50/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.33  
% 2.50/1.34  tff(f_64, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.50/1.34  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.50/1.34  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.50/1.34  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.50/1.34  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.50/1.34  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.50/1.34  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 2.50/1.34  tff(c_18, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.50/1.34  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.50/1.34  tff(c_20, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.50/1.34  tff(c_14, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.50/1.34  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.50/1.34  tff(c_8, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.50/1.34  tff(c_45, plain, (![A_18]: (k10_relat_1(A_18, k2_relat_1(A_18))=k1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.34  tff(c_54, plain, (![A_6]: (k10_relat_1(k6_relat_1(A_6), A_6)=k1_relat_1(k6_relat_1(A_6)) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_45])).
% 2.50/1.34  tff(c_58, plain, (![A_6]: (k10_relat_1(k6_relat_1(A_6), A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6, c_54])).
% 2.50/1.34  tff(c_77, plain, (![B_22, A_23]: (k7_relat_1(B_22, A_23)=B_22 | ~r1_tarski(k1_relat_1(B_22), A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.50/1.34  tff(c_80, plain, (![A_6, A_23]: (k7_relat_1(k6_relat_1(A_6), A_23)=k6_relat_1(A_6) | ~r1_tarski(A_6, A_23) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_77])).
% 2.50/1.34  tff(c_82, plain, (![A_6, A_23]: (k7_relat_1(k6_relat_1(A_6), A_23)=k6_relat_1(A_6) | ~r1_tarski(A_6, A_23))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_80])).
% 2.50/1.34  tff(c_10, plain, (![A_7, B_8]: (k5_relat_1(k6_relat_1(A_7), B_8)=k7_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.50/1.34  tff(c_92, plain, (![B_26, C_27, A_28]: (k10_relat_1(k5_relat_1(B_26, C_27), A_28)=k10_relat_1(B_26, k10_relat_1(C_27, A_28)) | ~v1_relat_1(C_27) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.50/1.34  tff(c_105, plain, (![A_7, B_8, A_28]: (k10_relat_1(k6_relat_1(A_7), k10_relat_1(B_8, A_28))=k10_relat_1(k7_relat_1(B_8, A_7), A_28) | ~v1_relat_1(B_8) | ~v1_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(B_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_92])).
% 2.50/1.34  tff(c_114, plain, (![A_29, B_30, A_31]: (k10_relat_1(k6_relat_1(A_29), k10_relat_1(B_30, A_31))=k10_relat_1(k7_relat_1(B_30, A_29), A_31) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_105])).
% 2.50/1.34  tff(c_136, plain, (![A_6, A_29]: (k10_relat_1(k7_relat_1(k6_relat_1(A_6), A_29), A_6)=k10_relat_1(k6_relat_1(A_29), A_6) | ~v1_relat_1(k6_relat_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_114])).
% 2.50/1.34  tff(c_193, plain, (![A_34, A_35]: (k10_relat_1(k7_relat_1(k6_relat_1(A_34), A_35), A_34)=k10_relat_1(k6_relat_1(A_35), A_34))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_136])).
% 2.50/1.34  tff(c_205, plain, (![A_6, A_23]: (k10_relat_1(k6_relat_1(A_6), A_6)=k10_relat_1(k6_relat_1(A_23), A_6) | ~r1_tarski(A_6, A_23))), inference(superposition, [status(thm), theory('equality')], [c_82, c_193])).
% 2.50/1.34  tff(c_209, plain, (![A_36, A_37]: (k10_relat_1(k6_relat_1(A_36), A_37)=A_37 | ~r1_tarski(A_37, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_205])).
% 2.50/1.34  tff(c_113, plain, (![A_7, B_8, A_28]: (k10_relat_1(k6_relat_1(A_7), k10_relat_1(B_8, A_28))=k10_relat_1(k7_relat_1(B_8, A_7), A_28) | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_105])).
% 2.50/1.34  tff(c_609, plain, (![B_53, A_54, A_55]: (k10_relat_1(k7_relat_1(B_53, A_54), A_55)=k10_relat_1(B_53, A_55) | ~v1_relat_1(B_53) | ~r1_tarski(k10_relat_1(B_53, A_55), A_54))), inference(superposition, [status(thm), theory('equality')], [c_209, c_113])).
% 2.50/1.34  tff(c_651, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_609])).
% 2.50/1.34  tff(c_663, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_651])).
% 2.50/1.34  tff(c_665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_663])).
% 2.50/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.34  
% 2.50/1.34  Inference rules
% 2.50/1.34  ----------------------
% 2.50/1.34  #Ref     : 0
% 2.50/1.34  #Sup     : 144
% 2.50/1.34  #Fact    : 0
% 2.50/1.34  #Define  : 0
% 2.50/1.34  #Split   : 0
% 2.50/1.34  #Chain   : 0
% 2.50/1.34  #Close   : 0
% 2.50/1.34  
% 2.50/1.34  Ordering : KBO
% 2.50/1.34  
% 2.50/1.34  Simplification rules
% 2.50/1.34  ----------------------
% 2.50/1.34  #Subsume      : 12
% 2.50/1.34  #Demod        : 126
% 2.50/1.34  #Tautology    : 61
% 2.50/1.34  #SimpNegUnit  : 1
% 2.50/1.34  #BackRed      : 0
% 2.50/1.34  
% 2.50/1.34  #Partial instantiations: 0
% 2.50/1.34  #Strategies tried      : 1
% 2.50/1.34  
% 2.50/1.34  Timing (in seconds)
% 2.50/1.34  ----------------------
% 2.50/1.34  Preprocessing        : 0.27
% 2.50/1.34  Parsing              : 0.15
% 2.50/1.34  CNF conversion       : 0.02
% 2.50/1.34  Main loop            : 0.31
% 2.50/1.34  Inferencing          : 0.13
% 2.50/1.34  Reduction            : 0.10
% 2.50/1.34  Demodulation         : 0.07
% 2.50/1.34  BG Simplification    : 0.02
% 2.50/1.34  Subsumption          : 0.04
% 2.50/1.34  Abstraction          : 0.02
% 2.50/1.34  MUC search           : 0.00
% 2.50/1.34  Cooper               : 0.00
% 2.50/1.34  Total                : 0.60
% 2.50/1.34  Index Insertion      : 0.00
% 2.50/1.34  Index Deletion       : 0.00
% 2.50/1.34  Index Matching       : 0.00
% 2.50/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
