%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:32 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 (  96 expanded)
%              Number of equality atoms :   26 (  36 expanded)
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

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_18,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    ! [B_22,A_23] :
      ( k7_relat_1(B_22,A_23) = B_22
      | ~ r1_tarski(k1_relat_1(B_22),A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,(
    ! [A_8,A_23] :
      ( k7_relat_1(k6_relat_1(A_8),A_23) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_23)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_54])).

tff(c_59,plain,(
    ! [A_8,A_23] :
      ( k7_relat_1(k6_relat_1(A_8),A_23) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_57])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k5_relat_1(k6_relat_1(A_9),B_10) = k7_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,(
    ! [A_26,B_27] :
      ( k10_relat_1(A_26,k1_relat_1(B_27)) = k1_relat_1(k5_relat_1(A_26,B_27))
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [A_26,A_8] :
      ( k1_relat_1(k5_relat_1(A_26,k6_relat_1(A_8))) = k10_relat_1(A_26,A_8)
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_83,plain,(
    ! [A_28,A_29] :
      ( k1_relat_1(k5_relat_1(A_28,k6_relat_1(A_29))) = k10_relat_1(A_28,A_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_78])).

tff(c_99,plain,(
    ! [A_29,A_9] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_29),A_9)) = k10_relat_1(k6_relat_1(A_9),A_29)
      | ~ v1_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_83])).

tff(c_104,plain,(
    ! [A_30,A_31] : k1_relat_1(k7_relat_1(k6_relat_1(A_30),A_31)) = k10_relat_1(k6_relat_1(A_31),A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_99])).

tff(c_119,plain,(
    ! [A_23,A_8] :
      ( k10_relat_1(k6_relat_1(A_23),A_8) = k1_relat_1(k6_relat_1(A_8))
      | ~ r1_tarski(A_8,A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_104])).

tff(c_122,plain,(
    ! [A_23,A_8] :
      ( k10_relat_1(k6_relat_1(A_23),A_8) = A_8
      | ~ r1_tarski(A_8,A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_119])).

tff(c_144,plain,(
    ! [B_34,C_35,A_36] :
      ( k10_relat_1(k5_relat_1(B_34,C_35),A_36) = k10_relat_1(B_34,k10_relat_1(C_35,A_36))
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_161,plain,(
    ! [A_9,B_10,A_36] :
      ( k10_relat_1(k6_relat_1(A_9),k10_relat_1(B_10,A_36)) = k10_relat_1(k7_relat_1(B_10,A_9),A_36)
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_144])).

tff(c_166,plain,(
    ! [A_37,B_38,A_39] :
      ( k10_relat_1(k6_relat_1(A_37),k10_relat_1(B_38,A_39)) = k10_relat_1(k7_relat_1(B_38,A_37),A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_161])).

tff(c_276,plain,(
    ! [B_50,A_51,A_52] :
      ( k10_relat_1(k7_relat_1(B_50,A_51),A_52) = k10_relat_1(B_50,A_52)
      | ~ v1_relat_1(B_50)
      | ~ r1_tarski(k10_relat_1(B_50,A_52),A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_166])).

tff(c_294,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_276])).

tff(c_301,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_294])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:47:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.33  
% 2.21/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.34  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.21/1.34  
% 2.21/1.34  %Foreground sorts:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Background operators:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Foreground operators:
% 2.21/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.21/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.21/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.21/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.21/1.34  
% 2.21/1.35  tff(f_67, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 2.21/1.35  tff(f_43, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.21/1.35  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.21/1.35  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.21/1.35  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.21/1.35  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.21/1.35  tff(f_32, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 2.21/1.35  tff(c_18, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.35  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.35  tff(c_20, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.35  tff(c_6, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.35  tff(c_14, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.21/1.35  tff(c_54, plain, (![B_22, A_23]: (k7_relat_1(B_22, A_23)=B_22 | ~r1_tarski(k1_relat_1(B_22), A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.35  tff(c_57, plain, (![A_8, A_23]: (k7_relat_1(k6_relat_1(A_8), A_23)=k6_relat_1(A_8) | ~r1_tarski(A_8, A_23) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_54])).
% 2.21/1.35  tff(c_59, plain, (![A_8, A_23]: (k7_relat_1(k6_relat_1(A_8), A_23)=k6_relat_1(A_8) | ~r1_tarski(A_8, A_23))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_57])).
% 2.21/1.35  tff(c_10, plain, (![A_9, B_10]: (k5_relat_1(k6_relat_1(A_9), B_10)=k7_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.35  tff(c_69, plain, (![A_26, B_27]: (k10_relat_1(A_26, k1_relat_1(B_27))=k1_relat_1(k5_relat_1(A_26, B_27)) | ~v1_relat_1(B_27) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.35  tff(c_78, plain, (![A_26, A_8]: (k1_relat_1(k5_relat_1(A_26, k6_relat_1(A_8)))=k10_relat_1(A_26, A_8) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_6, c_69])).
% 2.21/1.35  tff(c_83, plain, (![A_28, A_29]: (k1_relat_1(k5_relat_1(A_28, k6_relat_1(A_29)))=k10_relat_1(A_28, A_29) | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_78])).
% 2.21/1.35  tff(c_99, plain, (![A_29, A_9]: (k1_relat_1(k7_relat_1(k6_relat_1(A_29), A_9))=k10_relat_1(k6_relat_1(A_9), A_29) | ~v1_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_83])).
% 2.21/1.35  tff(c_104, plain, (![A_30, A_31]: (k1_relat_1(k7_relat_1(k6_relat_1(A_30), A_31))=k10_relat_1(k6_relat_1(A_31), A_30))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_99])).
% 2.21/1.35  tff(c_119, plain, (![A_23, A_8]: (k10_relat_1(k6_relat_1(A_23), A_8)=k1_relat_1(k6_relat_1(A_8)) | ~r1_tarski(A_8, A_23))), inference(superposition, [status(thm), theory('equality')], [c_59, c_104])).
% 2.21/1.35  tff(c_122, plain, (![A_23, A_8]: (k10_relat_1(k6_relat_1(A_23), A_8)=A_8 | ~r1_tarski(A_8, A_23))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_119])).
% 2.21/1.35  tff(c_144, plain, (![B_34, C_35, A_36]: (k10_relat_1(k5_relat_1(B_34, C_35), A_36)=k10_relat_1(B_34, k10_relat_1(C_35, A_36)) | ~v1_relat_1(C_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.35  tff(c_161, plain, (![A_9, B_10, A_36]: (k10_relat_1(k6_relat_1(A_9), k10_relat_1(B_10, A_36))=k10_relat_1(k7_relat_1(B_10, A_9), A_36) | ~v1_relat_1(B_10) | ~v1_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(B_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_144])).
% 2.21/1.35  tff(c_166, plain, (![A_37, B_38, A_39]: (k10_relat_1(k6_relat_1(A_37), k10_relat_1(B_38, A_39))=k10_relat_1(k7_relat_1(B_38, A_37), A_39) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_161])).
% 2.21/1.35  tff(c_276, plain, (![B_50, A_51, A_52]: (k10_relat_1(k7_relat_1(B_50, A_51), A_52)=k10_relat_1(B_50, A_52) | ~v1_relat_1(B_50) | ~r1_tarski(k10_relat_1(B_50, A_52), A_51))), inference(superposition, [status(thm), theory('equality')], [c_122, c_166])).
% 2.21/1.35  tff(c_294, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_276])).
% 2.21/1.35  tff(c_301, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_294])).
% 2.21/1.35  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_301])).
% 2.21/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.35  
% 2.21/1.35  Inference rules
% 2.21/1.35  ----------------------
% 2.21/1.35  #Ref     : 0
% 2.21/1.35  #Sup     : 64
% 2.32/1.35  #Fact    : 0
% 2.32/1.35  #Define  : 0
% 2.32/1.35  #Split   : 0
% 2.32/1.35  #Chain   : 0
% 2.32/1.35  #Close   : 0
% 2.32/1.35  
% 2.32/1.35  Ordering : KBO
% 2.32/1.35  
% 2.32/1.35  Simplification rules
% 2.32/1.35  ----------------------
% 2.32/1.35  #Subsume      : 4
% 2.32/1.35  #Demod        : 27
% 2.32/1.35  #Tautology    : 24
% 2.32/1.35  #SimpNegUnit  : 1
% 2.32/1.35  #BackRed      : 0
% 2.32/1.35  
% 2.32/1.35  #Partial instantiations: 0
% 2.32/1.35  #Strategies tried      : 1
% 2.32/1.35  
% 2.32/1.35  Timing (in seconds)
% 2.32/1.35  ----------------------
% 2.32/1.35  Preprocessing        : 0.32
% 2.32/1.35  Parsing              : 0.17
% 2.32/1.35  CNF conversion       : 0.02
% 2.32/1.35  Main loop            : 0.20
% 2.32/1.35  Inferencing          : 0.08
% 2.32/1.35  Reduction            : 0.06
% 2.32/1.35  Demodulation         : 0.05
% 2.32/1.35  BG Simplification    : 0.02
% 2.32/1.35  Subsumption          : 0.03
% 2.32/1.35  Abstraction          : 0.02
% 2.32/1.35  MUC search           : 0.00
% 2.32/1.35  Cooper               : 0.00
% 2.32/1.35  Total                : 0.56
% 2.32/1.35  Index Insertion      : 0.00
% 2.32/1.35  Index Deletion       : 0.00
% 2.32/1.35  Index Matching       : 0.00
% 2.32/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
